import Langlands.Global.RankinSelberg.ComplexGodementCompact
import Langlands.Analysis.CompactLinearParameterIntegralProof
import Langlands.Representation.Archimedean.ComplexJacquetLimit
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesExtension
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-! # Smooth compact Godement sections of the complex standard module -/

noncomputable section

open MeasureTheory Measure
open scoped ContDiff Manifold Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.GeneralLinear Langlands.Archimedean Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

private abbrev Square (m : ℕ) := Matrix (Fin m) (Fin m) ℂ
private abbrev Rect (m : ℕ) := Matrix (Fin m) (Fin (m + 1)) ℂ

private def trailingRowsLinear (m : ℕ) : Square (m + 1) →ₗ[ℝ] Rect m where
  toFun := trailingRows
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def rowActionLinear (m : ℕ) : Square m →ₗ[ℝ] (Square (m + 1) →L[ℝ] Rect m) where
  toFun A := ((mulLeftLinearMap (Fin (m + 1)) ℝ A).comp
    (trailingRowsLinear m)).toContinuousLinearMap
  map_add' A B := by
    ext X i j
    change ((A + B) * trailingRows X) i j =
      (A * trailingRows X + B * trailingRows X) i j
    rw [Matrix.add_mul]
  map_smul' c A := by
    ext X i j
    change ((c • A) * trailingRows X) i j = (c • (A * trailingRows X)) i j
    rw [Matrix.smul_mul]

private theorem contDiffAt_integerPower (k : ℤ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (fun w : ℂ => w ^ k) z := by
  have h : ContDiffAt ℝ ∞ (fun w : ℂ => w) z := contDiffAt_id
  cases k with
  | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using h.pow k
  | negSucc k =>
      rw [show (fun w : ℂ => w ^ Int.negSucc k) = (fun w : ℂ => w ^ (k + 1))⁻¹ by
        funext w
        exact zpow_negSucc w k]
      exact (h.pow (k + 1)).inv (pow_ne_zero _ hz)

private def characterWeightFunction (d : ComplexCharacterData) (s : ℂ) (z : ℂ) : ℂ :=
  ((z / (‖z‖ : ℂ)) ^ d.weight * (‖z‖ : ℂ) ^ (2 * d.exponent)) *
    ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s

private theorem contDiffOn_characterWeightFunction (d : ComplexCharacterData) (s : ℂ) :
    ContDiffOn ℝ ∞ (characterWeightFunction d s) {z : ℂ | z ≠ 0} := by
  intro z hz
  have hz' : z ≠ 0 := hz
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz'
  have hn : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) z := contDiffAt_norm ℝ hz'
  have hnc : ContDiffAt ℝ ∞ (fun w : ℂ => (‖w‖ : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z hn
  have hunit : ContDiffAt ℝ ∞ (fun w : ℂ => w / (‖w‖ : ℂ)) z := by
    simp only [div_eq_mul_inv]
    exact contDiffAt_id.mul (hnc.inv (by exact_mod_cast hpos.ne'))
  have hunit_ne : z / (‖z‖ : ℂ) ≠ 0 := div_ne_zero hz' (by exact_mod_cast hpos.ne')
  exact (((contDiffAt_integerPower d.weight hunit_ne).comp z hunit).mul
    (ComplexPrincipalSeriesExtension.contDiffAt_ofReal_cpow hn hpos (2 * d.exponent))).mul
      (ComplexPrincipalSeriesExtension.contDiffAt_ofReal_cpow (hn.pow 2) (pow_pos hpos 2) s)
      |>.contDiffWithinAt

private theorem contMDiff_characterWeight_det {n : ℕ} (d : ComplexCharacterData) (s : ℂ) :
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞
      (fun g : Langlands.GeneralLinear n ℂ => characterWeight d s (determinant g)) := by
  have hdet : ContDiff ℝ ∞ (fun X : Square n => X.det) :=
    ComplexMaximalParabolicIntegration.contDiff_det
  have hA : ContDiffOn ℝ ∞ (fun X : Square n => characterWeightFunction d s X.det)
      {X | IsUnit X} :=
    (contDiffOn_characterWeightFunction d s).comp hdet.contDiffOn fun X hX =>
      ((Matrix.isUnit_iff_isUnit_det X).mp hX).ne_zero
  refine contMDiff_of_contDiffOn hA fun g => ?_
  change (d.character (determinant g) : ℂ) * normPower s (determinant g) =
    characterWeightFunction d s g.val.det
  rw [d.character_eq]
  rfl

/-- Compact tests supported in the full-row-rank locus give smooth sections. -/
theorem contMDiff_godementSection {m : ℕ} (ν : Measure (Langlands.GeneralLinear m ℂ))
    [IsLocallyFiniteMeasure ν] (d : ComplexCharacterData) {Φ : Rect m → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ)
    (hfull : ∀ X ∈ tsupport Φ, HasFullRowRank X)
    {f : Langlands.GeneralLinear m ℂ → ℂ} (hf : Continuous f) :
    ContMDiff (matrixModel ℂ (m + 1)) 𝓘(ℝ, ℂ) ∞ (godementSection ν d Φ f) := by
  unfold godementSection
  refine ComplexJacquetLimit.contMDiff_mul_fun (contMDiff_characterWeight_det d _) ?_
  intro g
  obtain ⟨L, hL, hg⟩ := exists_compact_mem_nhds g
  obtain ⟨H, hH, hzero⟩ := exists_compact_godementSection_support hΦc hfull hL
  let c (h : Langlands.GeneralLinear m ℂ) :=
    f h⁻¹ * characterWeight d (((m : ℂ) + 1) / 2) (determinant h)
  have hc : Continuous c := (hf.comp continuous_inv).mul
    ((continuous_characterWeight d _).comp determinantContinuous.continuous)
  let A (h : Langlands.GeneralLinear m ℂ) : Square (m + 1) →L[ℝ] Rect m :=
    (rowActionLinear m).toContinuousLinearMap h.val
  have hA : Continuous A := (rowActionLinear m).toContinuousLinearMap.continuous.comp
    Units.continuous_val
  have hJ : ContDiff ℝ ∞ (fun X : Square (m + 1) => ∫ h in H, c h * Φ (A h X) ∂ν) :=
    contDiffOn_univ.mp (Langlands.Analysis.compactLinearParameterIntegral
      (Langlands.GeneralLinear m ℂ) (Square (m + 1)) (Rect m) ν H hH
      Set.univ isOpen_univ Set.univ isOpen_univ c hc A hA Φ hΦ.contDiffOn
      (fun _ _ _ _ => Set.mem_univ _)).1
  have hM := hJ.contMDiff.comp (Units.contMDiff_val (n := ∞))
  refine hM.contMDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [hg] with x hx
  symm
  calc
    _ = ∫ h, c h * Φ (A h x.val) ∂ν := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => ?_
      change c h * Φ (h.val * trailingRows x.val) = 0
      rw [hzero x hx h hh, mul_zero]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with h
      change (f h⁻¹ * characterWeight d (((m : ℂ) + 1) / 2) (determinant h)) *
        Φ (h.val * trailingRows x.val) = godementSectionIntegrand d Φ f x h
      unfold godementSectionIntegrand
      ring

/-- A smooth compact test supported in the full-row-rank locus produces a vector in the
larger standard module for the list `d :: ds`. -/
def ComplexGodementCompactSmoothStatement : Prop :=
  ∀ (m : ℕ) (ν : Measure (Langlands.GeneralLinear m ℂ)) [IsLocallyFiniteMeasure ν]
    [IsMulRightInvariant ν] (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (Φ : Rect m → ℂ), ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
    (∀ X ∈ tsupport Φ, HasFullRowRank X) →
    ∀ (f : Langlands.GeneralLinear m ℂ → ℂ), f ∈ complexStandardModule m ds →
      godementSection ν d Φ f ∈ complexStandardModule (m + 1) (d :: ds)

theorem complexGodementCompactSmooth : ComplexGodementCompactSmoothStatement := by
  intro m ν _ _ d ds Φ hΦ hΦc hfull f hf
  refine ⟨contMDiff_godementSection ν d hΦ hΦc hfull hf.1.continuous, ?_⟩
  intro a u g
  exact godementSection_covariant ν d ds Φ hf a u g

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
