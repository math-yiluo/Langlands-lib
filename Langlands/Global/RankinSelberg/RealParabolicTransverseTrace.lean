import Langlands.Analysis.TranslationCovariantDistribution
import Langlands.Global.RankinSelberg.RealParabolicSectionRightTranslation
import Langlands.Global.RankinSelberg.RealParabolicSmoothSectionMap
import Langlands.Global.RankinSelberg.RealExactWhittakerUniqueness
import Langlands.Representation.Shahidi.JacquetRadicalProof

/-! # The transverse Fourier trace of a smooth real Whittaker functional -/

noncomputable section

open MeasureTheory TopologicalSpace Matrix
open scoped ContDiff Distributions Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

open Langlands.Analysis Langlands.Archimedean Langlands.GeneralLinear
open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (rectangularMeasure)
open Langlands.Shahidi (swapRank upper intertwiningUnipotent)
open RealStandardCompactBanach RealExactWhittakerUniqueness ArchimedeanLocal

private local instance (d : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedAddCommGroup

private local instance (d : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedSpace

variable {m p : ℕ}

local notation "G" => fun d : ℕ => Langlands.GeneralLinear d ℝ
local notation "N" => (p + 1 + m) + 1
local notation "I" => matrixModel ℝ N
local notation "X" => Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ
local notation "Test" => 𝓓((⊤ : Opens X), ℂ)
local notation:max "R" ds:max => representation (n := N) ds
local notation:max "D" ds:max => DerivativeSmoothVectors I (R ds)

/-- The boundary character of the actual upper rectangle in the right group coordinates. -/
def transversePhase (a : ℝˣ) (Y : X) : ℂ := (realScaledCharacter a).complex (Y (Fin.last m) 0)

private theorem contDiff_transversePhase (a : ℝˣ) : ContDiff ℝ ∞ (transversePhase (m := m) (p := p) a) := by
  change ContDiff ℝ ∞ (fun Y : X => (realScaledCharacter a).complex (Y (Fin.last m) 0))
  simp only [UnitaryAdditiveCharacter.complex_apply, realScaledCharacter_apply, Real.fourierChar_apply]
  have h : ContDiff ℝ ∞ (fun Y : X => Y (Fin.last m) 0) :=
    (Matrix.entryLinearMap ℝ ℝ (Fin.last m) (0 : Fin (p + 1))).toContinuousLinearMap.contDiff
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_const.mul h))).mul
    contDiff_const).cexp

private theorem transversePhase_zero (a : ℝˣ) : transversePhase (m := m) (p := p) a 0 = 1 := by
  simp [transversePhase]

private theorem transversePhase_add (a : ℝˣ) (Y Z : X) :
    transversePhase a (Y + Z) = transversePhase a Y * transversePhase a Z :=
  (realScaledCharacter a).complex.map_add_eq_mul _ _

private theorem transversePhase_neg (a : ℝˣ) (Y : X) : transversePhase a (-Y) = transversePhase (-a) Y := by
  simp only [transversePhase, Matrix.neg_apply, UnitaryAdditiveCharacter.complex_apply,
    realScaledCharacter_apply, Units.val_neg, neg_mul, mul_neg]

/-- The negative boundary Fourier moment in the self-dual rectangular measure. -/
def transverseMoment (a : ℝˣ) (φ : Test) : ℂ :=
  ∫ Y, φ Y * transversePhase (-a) Y ∂(rectangularMeasure (realSelfDualMeasure a) (m + 1) (p + 1))

/-- A compact test can have Fourier moment exactly one at the boundary character. -/
theorem exists_transverseMoment_eq_one (a : ℝˣ) : ∃ φ : Test, transverseMoment a φ = 1 := by
  let ν := (realSelfDualMeasure a).measure
  let : ν.IsAddHaarMeasure := (realSelfDualMeasure a).isAddHaar
  let : SigmaFinite ν := inferInstance
  let μ := rectangularMeasure (realSelfDualMeasure a) (m + 1) (p + 1)
  let : (Measure.pi fun _ : Fin (p + 1) => ν).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let : μ.IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ : Fin (m + 1) => Measure.pi fun _ : Fin (p + 1) => ν)
  let b : ContDiffBump (0 : X) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let c : ℂ := ((∫ Y, b Y ∂μ) : ℝ)
  have hc : c ≠ 0 := by
    refine Complex.ofReal_ne_zero.mpr
      (b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero b.hasCompactSupport
        (fun _ => b.nonneg) (x := 0) ?_).ne'
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    exact one_ne_zero
  let w : X → ℂ := fun Y => c⁻¹ * ((b Y : ℂ) * transversePhase a Y)
  have hws : ContDiff ℝ ∞ w := contDiff_const.mul
    ((Complex.ofRealCLM.contDiff.comp b.contDiff).mul (contDiff_transversePhase a))
  have hwC : HasCompactSupport w :=
    ((b.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right).mul_left
  let φ : Test := ⟨w, hws, hwC, Set.subset_univ _⟩
  refine ⟨φ, ?_⟩
  have hpair (Y : X) : transversePhase a Y * transversePhase (-a) Y = 1 := by
    rw [← transversePhase_neg, ← transversePhase_add, add_neg_cancel, transversePhase_zero]
  change (∫ Y, c⁻¹ * ((b Y : ℂ) * transversePhase a Y) * transversePhase (-a) Y ∂μ) = 1
  simp only [mul_assoc, hpair, mul_one, integral_const_mul, integral_complex_ofReal]
  exact inv_mul_cancel₀ hc

private theorem whittakerCharacter_intertwiningUnipotent (a : ℝˣ) (Z : X) :
    realWhittakerCharacter a (intertwiningUnipotent (p + 1) (m + 1) ℝ Z) = transversePhase a Z := by
  exact congrArg (realScaledCharacter a).complex
    (Langlands.Shahidi.sum_superdiagonal_intertwiningUnipotent p m Z)

variable {d₁ d₂ : List RealBlock} (hm : realRank d₁ = m + 1) (hp : realRank d₂ = p + 1)
variable (f : realStandardModule (m + 1) d₁) (g : realStandardModule (p + 1) d₂)

private theorem translate_smoothSectionVector_rectangle (Z : X) (φ ψ : Test)
    (h : ∀ Y, ψ Y = φ (Y + Z)) :
    DerivativeSmoothVectors.representation I (R (d₂ ++ d₁))
      (intertwiningUnipotent (p + 1) (m + 1) ℝ Z) (smoothSectionVector hm hp f g φ) =
        smoothSectionVector hm hp f g ψ := by
  apply (derivativeEquiv (d₂ ++ d₁)).symm.injective
  apply Subtype.ext
  funext u
  have hrec := reconstruct_translate_smoothSectionVector (m := m) (n := p + 1) hm hp f g φ
    (intertwiningUnipotent (p + 1) (m + 1) ℝ Z) u
  refine hrec.trans ?_
  have hright := (realParabolicSectionRightTranslation (m + 1) (p + 1) f.val g.val φ f.2.1.1 g.2.1.1
    φ.contDiff φ.hasCompactSupport).1 u Z
  have hψ : (fun Y => φ (Y + Z)) = (ψ : X → ℂ) := (funext h).symm
  rw [hψ] at hright
  refine hright.trans ?_
  rw [smoothSectionVector, LinearEquiv.symm_apply_apply]
  rfl

/-- On compact transverse tests, a continuous Whittaker functional is proportional to the
negative boundary Fourier integral for each pair of genuine Levi vectors. -/
def RealParabolicTransverseTraceStatement : Prop :=
  ∀ (m p : ℕ) (d₁ d₂ : List RealBlock) (hm : realRank d₁ = m + 1) (hp : realRank d₂ = p + 1)
    (f : realStandardModule (m + 1) d₁) (g : realStandardModule (p + 1) d₂) (a : ℝˣ)
    (L : DerivativeSmoothVectors (matrixModel ℝ ((p + 1) + (m + 1)))
      (representation (n := (p + 1) + (m + 1)) (d₂ ++ d₁)) →L[ℂ] ℂ),
    IsSmoothWhittakerEvaluation (r := p + 1 + m) (d₂ ++ d₁) a L →
      ∃ c : ℂ, ∀ φ : 𝓓((⊤ : Opens (Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ)), ℂ),
        L (smoothSectionVector hm hp f g φ) = c * transverseMoment a φ

set_option maxHeartbeats 800000 in
theorem realParabolicTransverseTrace : RealParabolicTransverseTraceStatement := by
  intro m p d₁ d₂ hm hp f g a L hL
  let T := L.comp (smoothSectionMap hm hp f g)
  have hCov : TranslationCovariant (transversePhase a) T := by
    intro Z φ ψ h
    let u : Langlands.GeneralLinear.upperUnipotent (p + 1 + m + 1) ℝ := ⟨intertwiningUnipotent (p + 1) (m + 1) ℝ Z,
      Langlands.Shahidi.intertwiningUnipotent_mem_upperUnipotent (p + 1) (m + 1) ℝ Z⟩
    change L (smoothSectionVector hm hp f g ψ) = transversePhase a Z * L (smoothSectionVector hm hp f g φ)
    have hv := translate_smoothSectionVector_rectangle hm hp f g Z φ ψ h
    have he := congrArg (fun v => L v) hv
    have hc := hL u (smoothSectionVector hm hp f g φ)
    have hphase := whittakerCharacter_intertwiningUnipotent (m := m) (p := p) a Z
    calc
      _ = L (DerivativeSmoothVectors.representation (matrixModel ℝ (p + 1 + m + 1))
          (representation (n := p + 1 + m + 1) (d₂ ++ d₁)) u.val
          (smoothSectionVector hm hp f g φ)) := he.symm
      _ = realWhittakerCharacter a u.val * L (smoothSectionVector hm hp f g φ) := hc
      _ = _ := congrArg (fun z => z * L (smoothSectionVector hm hp f g φ)) hphase
  let ν := (realSelfDualMeasure a).measure
  let : ν.IsAddHaarMeasure := (realSelfDualMeasure a).isAddHaar
  let : SigmaFinite ν := inferInstance
  let μ := rectangularMeasure (realSelfDualMeasure a) (m + 1) (p + 1)
  let : (Measure.pi fun _ : Fin (p + 1) => ν).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let : μ.IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ : Fin (m + 1) => Measure.pi fun _ : Fin (p + 1) => ν)
  obtain ⟨c, hc⟩ := translationCovariantDistribution μ (transversePhase a)
    (contDiff_transversePhase a) (transversePhase_zero a) (transversePhase_add a) T hCov
  refine ⟨c, fun φ => ?_⟩
  change T φ = _
  rw [hc φ]
  simp only [transversePhase_neg, transverseMoment, μ]

end Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection
