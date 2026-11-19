import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.Global.AdelicRepresentationHeightPropernessProof

/-! # Compact-uniform moderate growth in the normalized adelic height -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {N : ℕ} {rho : MatrixRepresentation G (Fin N)} {φ : AdelicGroupPoints F G → ℂ}

/-- The normalized matrix height with lower bound one, also for the zero-dimensional
representation. -/
def adelicHeightAtLeastOne (rho : MatrixRepresentation G (Fin N))
    (g : AdelicGroupPoints F G) : ℝ :=
  max 1 (adelicHeight F G rho g)

@[simp]
theorem adelicHeightAtLeastOne_eq (hN : 0 < N) (g : AdelicGroupPoints F G) :
    adelicHeightAtLeastOne rho g = adelicHeight F G rho g :=
  max_eq_right (one_le_adelicHeight F G rho hN g)

/-- A nonnegative growth exponent can be used uniformly for all compact sets of right
translations in the normalized adelic height. -/
theorem HasModerateGrowthFunction.exists_compact_mul_le_height
    (hφ : HasModerateGrowthFunction F G rho φ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
      ∃ B : ℝ, 0 < B ∧ ∀ x : AdelicGroupPoints F G, ∀ g ∈ C,
        ‖φ (x * g)‖ ≤ B * adelicHeightAtLeastOne rho x ^ r := by
  obtain ⟨A, hA, r, hbound⟩ := hφ
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hmat (g : AdelicGroupPoints F G) : adelicMatrix F G rho g = 1 := by
      apply Units.ext
      ext i j
      exact Fin.elim0 i
    have hle (g : AdelicGroupPoints F G) :
        ‖φ g‖ ≤ A * AdelicMatrixHeight.sourceNorm F 0 1 ^ r := by
      simpa only [adelicSourceNorm, hmat] using hbound g
    refine ⟨0, le_rfl, fun _ _ => ⟨max 1 (A * AdelicMatrixHeight.sourceNorm F 0 1 ^ r),
      zero_lt_one.trans_le (le_max_left _ _), fun x g _ => ?_⟩⟩
    rw [Real.rpow_zero, mul_one]
    exact (hle (x * g)).trans (le_max_right _ _)
  have h1 (g : AdelicGroupPoints F G) := one_le_adelicHeight F G rho hN g
  let d : ℝ := (N : ℝ) ^ (∑ v : InfinitePlace F, v.mult)
  have hd : 0 < d := pow_pos (Nat.cast_pos.mpr hN) _
  have hdH (g : AdelicGroupPoints F G) :
      adelicSourceNorm F G rho g = d⁻¹ * adelicHeight F G rho g := by
    rw [adelicHeight_eq_scalar_mul_sourceNorm, ← mul_assoc]
    change _ = d⁻¹ * d * _
    rw [inv_mul_cancel₀ hd.ne', one_mul]
  set r₀ := max r 0
  have hr₀ : 0 ≤ r₀ := le_max_right _ _
  refine ⟨r₀, hr₀, fun C hC => ?_⟩
  obtain ⟨M, hM⟩ := (hC.image (continuous_adelicHeight F G rho hN)).bddAbove
  set M₀ := max 1 M
  have hM₀ : 0 < M₀ := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨A * d⁻¹ ^ r * M₀ ^ r₀, mul_pos (mul_pos hA (Real.rpow_pos_of_pos (inv_pos.mpr hd) r))
    (Real.rpow_pos_of_pos hM₀ r₀), fun x g hg => ?_⟩
  have hg' : adelicHeight F G rho g ≤ M₀ := (hM ⟨g, hg, rfl⟩).trans (le_max_right _ _)
  have h0 (z : AdelicGroupPoints F G) : 0 ≤ adelicHeight F G rho z := zero_le_one.trans (h1 z)
  have hH : adelicHeight F G rho (x * g) ≤ adelicHeight F G rho x * M₀ := by
    exact (adelicHeight_mul_le F G rho hN x g).trans (mul_le_mul_of_nonneg_left hg' (h0 x))
  rw [adelicHeightAtLeastOne_eq hN]
  calc
    ‖φ (x * g)‖ ≤ A * adelicSourceNorm F G rho (x * g) ^ r := hbound _
    _ = A * d⁻¹ ^ r * adelicHeight F G rho (x * g) ^ r := by
      rw [hdH, Real.mul_rpow (inv_pos.mpr hd).le (h0 _), mul_assoc]
    _ ≤ A * d⁻¹ ^ r * (adelicHeight F G rho x * M₀) ^ r₀ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA.le (Real.rpow_nonneg (inv_pos.mpr hd).le _))
      exact (Real.rpow_le_rpow_of_exponent_le (h1 _) (le_max_left _ _)).trans
        (Real.rpow_le_rpow (h0 _) hH hr₀)
    _ = A * d⁻¹ ^ r * M₀ ^ r₀ * adelicHeight F G rho x ^ r₀ := by
      rw [Real.mul_rpow (h0 _) hM₀.le]
      ring

end Langlands.Global.RepresentationGrowth
