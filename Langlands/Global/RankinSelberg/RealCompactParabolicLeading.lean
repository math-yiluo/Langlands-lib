import Langlands.Global.RankinSelberg.RealParabolicPrimalIntegral
import Langlands.Global.RankinSelberg.RealParabolicRowLift
import Langlands.Global.RankinSelberg.RealParabolicTraceNonzero
import Langlands.Global.RankinSelberg.RealGapNormalizedWeighted

/-! # Leading-block restriction of a compact parabolic lift -/

noncomputable section

open Set TopologicalSpace MeasureTheory
open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Distributions Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

open RealExactWhittakerUniqueness RealStandardCompactBanach
open RealParabolicPrimalIntegral RealParabolicRowLift ArchimedeanLocal
open Langlands.Shahidi (swapRank)

private local instance (d : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedAddCommGroup

private local instance (d : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedSpace

local notation "G" => fun d => Langlands.GeneralLinear d ℝ
local notation "S" => realStandardModule
local notation:max "R" d:max ds:max => representation (n := d) ds
local notation:max "D" d:max ds:max => DerivativeSmoothVectors (matrixModel ℝ d) (R d ds)
local notation:max "act" d:max ds:max => DerivativeSmoothVectors.representation (matrixModel ℝ d) (R d ds)
local notation "X" => fun m p => Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ
local notation "Test" => fun m p => 𝓓((⊤ : Opens (X m p)), ℂ)

variable {m p : ℕ}

/-- The last-row Schwartz profile of a compact transverse test. -/
def compactRowProfile (a : ℝˣ) (φ : Test m p) : 𝓢((Fin (m + 1) → ℝ), ℂ) :=
  rowFourierProfile a (φ.hasCompactSupport.toSchwartzMap φ.contDiff)

/-- These profiles are dense in the whole row Schwartz space. -/
theorem denseRange_compactRowProfile (a : ℝˣ) : DenseRange (compactRowProfile (m := m) (p := p) a) := by
  apply (realParabolicCompactRowProfileDensity m p a).mono
  rintro _ ⟨Φ, hΦ, rfl⟩
  let φ : Test m p := ⟨Φ, Φ.smooth', hΦ, subset_univ _⟩
  exact ⟨φ, congrArg (rowFourierProfile (r := m) (p := p) a) (SchwartzMap.ext fun _ => rfl)⟩

private theorem transverseMoment_translateLeading (a : ℝˣ) (φ : Test m p) (A : G (m + 1)) :
    transverseMoment a (transverseLeviTranslate A (1 : G (p + 1)) φ) =
      ((|A.val.det| ^ (p + 1) : ℝ) : ℂ) * compactRowProfile a φ (Langlands.RankinSelberg.lastRow A) := by
  let Φ := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  refine Eq.trans ?_ (parabolicMomentKernel_integral a Φ A).2
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun Y => ?_
  change φ (A⁻¹.val * Y * (1 : G (p + 1)).val) * transversePhase (-a) Y =
    Φ (A⁻¹.val * Y) * transversePhase (-a) Y
  rw [Units.val_one, Matrix.mul_one]
  rfl

private theorem lastRow_one : Langlands.RankinSelberg.lastRow (1 : G (m + 1)) = Pi.single (Fin.last m) 1 := by
  funext i
  simp [Langlands.RankinSelberg.lastRow, Matrix.one_apply, Pi.single_apply, eq_comm]

/-- A compact rectangle profile can be normalized to one at the identity last row. -/
theorem exists_compactRowProfile_basis_eq_one (a : ℝˣ) :
    ∃ φ : Test m p, compactRowProfile a φ (Pi.single (Fin.last m) 1) = 1 := by
  obtain ⟨φ, hφ⟩ := exists_transverseMoment_eq_one (m := m) (p := p) a
  have ht := transverseMoment_translateLeading a φ (1 : G (m + 1))
  have he : transverseLeviTranslate (1 : G (m + 1)) (1 : G (p + 1)) φ = φ := by
    ext Y
    change φ ((1 : G (m + 1))⁻¹.val * Y * (1 : G (p + 1)).val) = φ Y
    simp
  refine ⟨φ, ?_⟩
  simpa only [he, hφ, Units.val_one, Matrix.det_one, abs_one, one_pow, Complex.ofReal_one, one_mul,
    lastRow_one] using ht.symm

private theorem padGL_eq_exchanged_blockSum (A : G (m + 1)) :
    padGL (show m + 1 ≤ p + 1 + m + 1 by omega) A =
      swapRank (p + 1) (m + 1) ℝ (blockSum (A, (1 : G (p + 1)))) := by
  have hp := RealGapNormalizedWeighted.padGL_eq_rankInclusion (m + 1) p A
  apply Units.ext
  ext i j
  let e := finCongr (Nat.add_comm (p + 1) (m + 1))
  have he := congrArg (fun z : G (m + 1 + (p + 1)) => z.val (e i) (e j)) hp
  change (padGL _ A).val i j = (rankInclusion (p + 1) A).val (e i) (e j)
  simpa only [UnequalAnalytic.padGL_apply, e, finCongr_apply, Fin.val_cast, Matrix.one_apply,
    Fin.cast_inj] using he

private theorem detWeight_mul_jacobian (A : G (m + 1)) :
    detWeight (-(p + 1 : ℂ) / 2) A.val * ((|A.val.det| ^ (p + 1) : ℝ) : ℂ) =
      ArchimedeanLocal.detPower realNormalizedAbs A (((p + 1 : ℕ) : ℂ) / 2) := by
  have hpos : 0 < |A.val.det| := abs_pos.mpr (determinant A).ne_zero
  have hpow : ((|A.val.det| ^ (p + 1) : ℝ) : ℂ) =
      Complex.exp (((p + 1 : ℕ) : ℂ) * (Real.log |A.val.det| : ℂ)) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_exp, Real.exp_nat_mul, Real.exp_log hpos]
  rw [detWeight, hpow, ← Complex.exp_add, ArchimedeanLocal.detPower, realNormalizedAbs,
    Nat.cast_add, Nat.cast_one]
  congr 1
  ring

/-- A genuine leading-block coefficient times the row profile of a compact transverse test
and the prescribed half-power of the determinant is the restriction of an ambient coefficient. -/
def RealCompactParabolicLeadingRestrictionStatement : Prop :=
  ∀ (m p : ℕ) (d₁ d₂ : List RealBlock) (hm : realRank d₁ = m + 1) (hp : realRank d₂ = p + 1)
    (a : ℝˣ) (L : D (p + 1 + m + 1) (d₂ ++ d₁) →L[ℂ] ℂ)
    (L₁ : D (m + 1) d₁ →L[ℂ] ℂ) (L₂ : D (p + 1) d₂ →L[ℂ] ℂ),
    IsSmoothWhittakerEvaluation (r := p + 1 + m) (d₂ ++ d₁) a L →
    IsSmoothWhittakerEvaluation d₁ a L₁ → IsSmoothWhittakerEvaluation d₂ a L₂ →
    L ≠ 0 → L₁ ≠ 0 → L₂ ≠ 0 → ∃ g : S (p + 1) d₂,
      ∀ (f : S (m + 1) d₁) (φ : Test m p),
        HasLeadingBlockRestriction (show m < p + 1 + m by omega)
          (fun x => L (act (p + 1 + m + 1) (d₂ ++ d₁) x (smoothSectionVector hm hp f g φ)))
          (fun A => L₁ (act (m + 1) d₁ A (derivativeEquiv d₁ f))) (compactRowProfile a φ)

set_option maxHeartbeats 750000 in
theorem realCompactParabolicLeadingRestriction : RealCompactParabolicLeadingRestrictionStatement := by
  intro m p d₁ d₂ hm hp a L L₁ L₂ hL hL₁ hL₂ hLne hL₁ne hL₂ne
  obtain ⟨c, hc, hTrace⟩ := realParabolicTraceNonzero m p d₁ d₂ hm hp a L L₁ L₂ hL hL₁ hL₂ hLne hL₁ne hL₂ne
  have hEx : ∃ v, L₂ v ≠ 0 := by
    by_contra! hz
    exact hL₂ne (ContinuousLinearMap.ext hz)
  obtain ⟨v, hv⟩ := hEx
  let g := (derivativeEquiv d₂).symm ((c * L₂ v)⁻¹ • v)
  have hScale : c * L₂ (derivativeEquiv d₂ g) = 1 := by
    dsimp only [g]
    rw [LinearEquiv.apply_symm_apply, map_smul, smul_eq_mul]
    calc
      _ = (c * L₂ v)⁻¹ * (c * L₂ v) := by ring
      _ = 1 := inv_mul_cancel₀ (mul_ne_zero hc hv)
  refine ⟨g, fun f φ A => ?_⟩
  have hTranslate := translate_smoothSectionVector_levi hm hp f g A (1 : G (p + 1)) φ
  have hOne : translate d₂ (1 : G (p + 1)) g = g := by
    apply Subtype.ext
    funext x
    exact (translate_apply d₂ 1 g x).trans (congrArg g.val (mul_one x))
  have hDetOne : detWeight ((m + 1 : ℂ) / 2) (1 : G (p + 1)).val = 1 := by simp [detWeight]
  change L (act (p + 1 + m + 1) (d₂ ++ d₁) (padGL _ A) (smoothSectionVector hm hp f g φ)) =
    L₁ (act (m + 1) d₁ A (derivativeEquiv d₁ f)) *
      compactRowProfile a φ (Langlands.RankinSelberg.lastRow A) *
      ArchimedeanLocal.detPower realNormalizedAbs A (((p + 1 + m - m : ℕ) : ℂ) / 2)
  rw [padGL_eq_exchanged_blockSum (p := p), hTranslate, map_smul, smul_eq_mul, hTrace,
    hOne, hDetOne, mul_one, derivativeEquiv_translate, transverseMoment_translateLeading, Nat.add_sub_cancel]
  let B := L₁ (act (m + 1) d₁ A (derivativeEquiv d₁ f))
  let T := compactRowProfile a φ (Langlands.RankinSelberg.lastRow A)
  calc
    _ = (c * L₂ (derivativeEquiv d₂ g)) * (B * T) *
        (detWeight (-(p + 1 : ℂ) / 2) A.val * ((|A.val.det| ^ (p + 1) : ℝ) : ℂ)) := by dsimp [B, T]; ring
    _ = _ := by rw [hScale, one_mul, detWeight_mul_jacobian]

end Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection
