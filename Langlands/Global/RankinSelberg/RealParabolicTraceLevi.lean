import Langlands.Global.RankinSelberg.RealParabolicTransverseTrace
import Langlands.Representation.Whittaker.TwoBlockJacquetCovarianceProof

/-! # Levi unipotent covariance of the real parabolic trace -/

noncomputable section

open MeasureTheory TopologicalSpace Matrix
open scoped ContDiff Distributions Manifold Matrix.Norms.Operator NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

open Langlands.Archimedean Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.LocalFactor.Archimedean ArchimedeanLocal RealStandardCompactBanach
open RealExactWhittakerUniqueness
open Langlands.RankinSelberg (rectangularMeasure rectangularMeasure_isAddHaar)
open Langlands.Shahidi (swapRank)

private local instance (d : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedAddCommGroup

private local instance (d : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedSpace

variable {m p : ℕ}

local notation "G" => fun d : ℕ => Langlands.GeneralLinear d ℝ
local notation "U" => fun d : ℕ => Langlands.GeneralLinear.upperUnipotent d ℝ
local notation "N" => (p + 1 + m) + 1
local notation "I" => matrixModel ℝ N
local notation "X" => Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ
local notation "Test" => 𝓓((⊤ : Opens X), ℂ)
local notation:max "R" ds:max => representation (n := N) ds
local notation:max "D" ds:max => DerivativeSmoothVectors I (R ds)
local notation "S" => realStandardModule

/-- The transverse test pulled back by the right Levi action. -/
def transverseLeviTranslate (A : G (m + 1)) (B : G (p + 1)) (φ : Test) : Test :=
  ⟨fun Y => φ (A⁻¹.val * Y * B.val),
    (RealGodement.rectangularTranslate A⁻¹ B (φ.hasCompactSupport.toSchwartzMap φ.contDiff)).smooth',
    φ.hasCompactSupport.comp_homeomorph (rectangularLeftRightHomeomorph A⁻¹ B), Set.subset_univ _⟩

private theorem detWeight_unipotent {d : ℕ} (z : ℂ) (u : U d) : detWeight z u.val.val = 1 := by
  rw [detWeight, MaximalParabolicIntegration.det_upperUnipotent u, abs_one, Real.log_one,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero]

private theorem rectangle_corner_unipotent (A : U (m + 1)) (B : U (p + 1)) (Y : X) :
    ((A.val⁻¹).val * Y * B.val.val) (Fin.last m) 0 = Y (Fin.last m) 0 := by
  have hA : A.val⁻¹ ∈ Langlands.GeneralLinear.upperUnipotent (m + 1) ℝ := inv_mem A.2
  rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (p + 1))]
  · rw [B.2.2, mul_one, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
    · rw [hA.2, one_mul]
    · intro i _ hi
      have hz : (A.val⁻¹).val (Fin.last m) i = 0 := hA.1 (lt_of_le_of_ne (Fin.le_last i) hi)
      rw [hz, zero_mul]
    · simp
  · intro j _ hj
    have hj' : (0 : Fin (p + 1)) < j := lt_of_le_of_ne (Fin.zero_le j) hj.symm
    rw [B.2.1 hj', mul_zero]
  · simp

private theorem scalarHaar_map_mul (ν : AdditiveHaarMeasure ℝ) (x : ℝ) (hx : x ≠ 0) :
    ν.measure.map (fun y : ℝ => x * y) = (‖x‖₊)⁻¹ • ν.measure := by
  change ν.measure.map (fun y : ℝ => x • y) = _
  rw [Measure.map_addHaar_smul ν.measure hx, Module.finrank_self, pow_one, abs_inv]
  rw [← Real.norm_eq_abs, ← coe_nnnorm, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
  rfl

/-- The transverse boundary moment is invariant under the two unipotent Levi factors. -/
theorem transverseMoment_leviUnipotent (a : ℝˣ) (A : U (m + 1)) (B : U (p + 1)) (φ : Test) :
    transverseMoment a (transverseLeviTranslate A.val B.val φ) = transverseMoment a φ := by
  let ν := realSelfDualMeasure a
  let : ν.measure.IsAddHaarMeasure := ν.isAddHaar
  let : SigmaFinite ν.measure := inferInstance
  let μ := rectangularMeasure ν (m + 1) (p + 1)
  let : μ.IsAddHaarMeasure := rectangularMeasure_isAddHaar _ _ _
  let E := rectangularLeftRightHomeomorph A.val⁻¹ B.val
  have hA := MaximalParabolicIntegration.det_upperUnipotent (A⁻¹)
  have hB := MaximalParabolicIntegration.det_upperUnipotent B
  have hmap : μ.map E = μ := by
    change μ.map (fun Y : X => (A.val⁻¹).val * Y * B.val.val) = μ
    have h := haarMeasure_map_rectangular ν.measure (nnnormHom : ℝ →*₀ ℝ≥0)
      (scalarHaar_map_mul ν) μ (A.val⁻¹).val B.val.val
      (determinant A.val⁻¹).ne_zero (determinant B.val).ne_zero
    simpa [hA, hB] using h
  let F := fun Y : X => φ Y * transversePhase (-a) Y
  calc
    transverseMoment a (transverseLeviTranslate A.val B.val φ) = ∫ Y, F (E Y) ∂μ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun Y => ?_
      change φ (E Y) * transversePhase (-a) Y = φ (E Y) * transversePhase (-a) (E Y)
      unfold transversePhase
      rw [rectangularLeftRightHomeomorph_apply, rectangle_corner_unipotent A B Y]
    _ = transverseMoment a φ := by
      rw [← E.measurableEmbedding.integral_map, hmap]
      rfl

variable {d₁ d₂ : List RealBlock} (hm : realRank d₁ = m + 1) (hp : realRank d₂ = p + 1)
variable (f : S (m + 1) d₁) (g : S (p + 1) d₂)

/-- A genuine right Levi translate of a smooth section is given by the determinant weights,
the two genuine Levi translates and the pulled-back transverse test. -/
theorem translate_smoothSectionVector_levi (A : G (m + 1)) (B : G (p + 1)) (φ : Test) :
    DerivativeSmoothVectors.representation I (R (d₂ ++ d₁))
      (swapRank (p + 1) (m + 1) ℝ (blockSum (A, B))) (smoothSectionVector hm hp f g φ) =
      (detWeight (-(p + 1 : ℂ) / 2) A.val * detWeight ((m + 1 : ℂ) / 2) B.val) •
        smoothSectionVector hm hp (translate d₁ A f) (translate d₂ B g) (transverseLeviTranslate A B φ) := by
  apply (derivativeEquiv (d₂ ++ d₁)).symm.injective
  apply Subtype.ext
  funext u
  have hrec := reconstruct_translate_smoothSectionVector (m := m) (n := p + 1) hm hp f g φ
    (swapRank (p + 1) (m + 1) ℝ (blockSum (A, B))) u
  refine hrec.trans ?_
  have hright := (realParabolicSectionRightTranslation (m + 1) (p + 1) f.val g.val φ f.2.1.1 g.2.1.1
    φ.contDiff φ.hasCompactSupport).2 u A B
  simp only [Nat.cast_add, Nat.cast_one] at hright
  refine hright.trans ?_
  rw [map_smul]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  congr 1
  have hval := reconstruct_translate_smoothSectionVector (m := m) (n := p + 1) hm hp
    (translate d₁ A f) (translate d₂ B g) (transverseLeviTranslate A B φ) 1 u
  simp only [map_one, Module.End.one_apply, mul_one] at hval
  refine Eq.trans ?_ hval.symm
  have hf' : (translate d₁ A f).val = fun a => f.val (a * A) := funext (translate_apply d₁ A f)
  have hg' : (translate d₂ B g).val = fun b => g.val (b * B) := funext (translate_apply d₂ B g)
  rw [hf', hg']
  rfl

/-- The scalar coefficient of the transverse Fourier moment, evaluated at a test of moment one. -/
def transverseTraceCoefficient (L : D (d₂ ++ d₁) →L[ℂ] ℂ) (τ : Test) : ℂ :=
  L (smoothSectionVector hm hp f g τ)

/-- The scalar coefficient in the trace of a normalized test recovers the trace at every test. -/
theorem eval_eq_transverseTraceCoefficient (a : ℝˣ) (L : D (d₂ ++ d₁) →L[ℂ] ℂ)
    (hL : IsSmoothWhittakerEvaluation (r := p + 1 + m) (d₂ ++ d₁) a L)
    (τ : Test) (hτ : transverseMoment a τ = 1) (φ : Test) :
    L (smoothSectionVector hm hp f g φ) =
      transverseTraceCoefficient hm hp f g L τ * transverseMoment a φ := by
  obtain ⟨c, hc⟩ := realParabolicTransverseTrace m p d₁ d₂ hm hp f g a L hL
  have h := hc τ
  rw [hτ, mul_one] at h
  exact (hc φ).trans (congrArg (fun z => z * transverseMoment a φ) h.symm)

private theorem traceCoefficient_leviUnipotent (a : ℝˣ) (L : D (d₂ ++ d₁) →L[ℂ] ℂ)
    (hL : IsSmoothWhittakerEvaluation (r := p + 1 + m) (d₂ ++ d₁) a L)
    (τ : Test) (hτ : transverseMoment a τ = 1) (A : U (m + 1)) (B : U (p + 1)) :
    transverseTraceCoefficient hm hp (translate d₁ A.val f) (translate d₂ B.val g) L τ =
      realWhittakerCharacter a A.val * realWhittakerCharacter a B.val *
        transverseTraceCoefficient hm hp f g L τ := by
  let q : U N := ⟨swapRank (p + 1) (m + 1) ℝ (blockSum (A.val, B.val)),
    Langlands.Shahidi.swapRank_mem_upperUnipotent _ _ ℝ
      (Langlands.Whittaker.blockSum_mem_upperUnipotent A B)⟩
  have hψ : realWhittakerCharacter a q.val =
      realWhittakerCharacter a A.val * realWhittakerCharacter a B.val :=
    (Langlands.Whittaker.standardCharacter_exchanged_blockSum (realScaledCharacter a) B A).trans
      (mul_comm _ _)
  let v := smoothSectionVector hm hp f g τ
  let f' := translate d₁ A.val f
  let g' := translate d₂ B.val g
  let τ' := transverseLeviTranslate A.val B.val τ
  have hτ' : transverseMoment a τ' = 1 := (transverseMoment_leviUnipotent a A B τ).trans hτ
  have hv := translate_smoothSectionVector_levi hm hp f g A.val B.val τ
  rw [detWeight_unipotent _ A, detWeight_unipotent _ B, one_mul, one_smul] at hv
  have h := eval_eq_transverseTraceCoefficient hm hp f' g' a L hL τ hτ τ'
  rw [hτ', mul_one] at h
  calc
    _ = L (smoothSectionVector hm hp f' g' τ') := h.symm
    _ = L (DerivativeSmoothVectors.representation I (R (d₂ ++ d₁)) q.val v) :=
      (congrArg (fun w => L w) hv).symm
    _ = _ := (hL q v).trans (congrArg (fun z => z * L v) hψ)

/-- The transverse trace coefficient is Whittaker covariant in the two Levi factors. -/
def RealParabolicTraceLeviStatement : Prop :=
  ∀ (m p : ℕ) (d₁ d₂ : List RealBlock) (hm : realRank d₁ = m + 1) (hp : realRank d₂ = p + 1)
    (f : S (m + 1) d₁) (g : S (p + 1) d₂) (a : ℝˣ)
    (L : DerivativeSmoothVectors (matrixModel ℝ (p + 1 + m + 1))
      (representation (n := p + 1 + m + 1) (d₂ ++ d₁)) →L[ℂ] ℂ),
    IsSmoothWhittakerEvaluation (r := p + 1 + m) (d₂ ++ d₁) a L →
    ∀ τ : 𝓓((⊤ : Opens (Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ)), ℂ), transverseMoment a τ = 1 →
      ∀ (A : U (m + 1)) (B : U (p + 1)),
        transverseTraceCoefficient hm hp (translate d₁ A.val f) (translate d₂ B.val g) L τ =
          realWhittakerCharacter a A.val * realWhittakerCharacter a B.val *
            transverseTraceCoefficient hm hp f g L τ

theorem realParabolicTraceLevi : RealParabolicTraceLeviStatement := by
  intro m p d₁ d₂ hm hp f g a L hL τ hτ A B
  exact traceCoefficient_leviUnipotent hm hp f g a L hL τ hτ A B

end Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection
