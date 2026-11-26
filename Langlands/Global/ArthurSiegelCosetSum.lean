import Langlands.Global.AdelicRepresentationHeight
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Decay of sums over distinct rational translates -/

noncomputable section

universe u v

open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

/-- Weighted bounds on terms evaluated at distinct rational translates of `x`
can be summed with an arbitrarily prescribed power of the height of `x`, provided
that the height at `x` is uniformly comparable with the translate heights. -/
def SiegelCosetSumDecayStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)), 0 < N → ∀ d : ℕ,
    Summable (fun q : RationalGroupPoints F G => (adelicHeight F G rho (rational F G q) ^ d)⁻¹) →
    ∀ (C : ℝ), 1 ≤ C → ∀ n : ℕ, ∃ (m : ℕ) (A : ℝ), 0 ≤ A ∧
      ∀ (x : AdelicGroupPoints F G) (J : Type v) (γ : J ↪ RationalGroupPoints F G)
        (b : J → ℂ) (B : ℝ), 0 ≤ B →
        (∀ j, adelicHeight F G rho x ≤ C * adelicHeight F G rho (rational F G (γ j) * x)) →
        (∀ j, ‖b j‖ * adelicHeight F G rho (rational F G (γ j) * x) ^ m ≤ B) →
        (Summable fun j => ‖b j‖) ∧
          ‖∑' j, b j‖ * adelicHeight F G rho x ^ n ≤ A * B

/-- Submultiplicativity and norm minimality turn the termwise bound into a
summable majorant depending on the heights of the representatives. -/
theorem siegelCosetSumDecay : SiegelCosetSumDecayStatement.{u, v} := by
  intro F _ _ G N rho hN d hd C hC n
  let H := adelicHeight F G rho
  have hpos (x : AdelicGroupPoints F G) : 0 < H x :=
    zero_lt_one.trans_le (one_le_adelicHeight F G rho hN x)
  let w (q : RationalGroupPoints F G) := (H (rational F G q) ^ d)⁻¹
  have hwn (q : RationalGroupPoints F G) : 0 ≤ w q := inv_nonneg.mpr (pow_nonneg (hpos _).le _)
  let S := ∑' q, w q
  have hS : 0 ≤ S := tsum_nonneg hwn
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  refine ⟨d + (d + n), C ^ (d + n) * S, mul_nonneg (pow_nonneg hC₀ _) hS, ?_⟩
  intro x J γ b B hB hmin hbound
  let y (j : J) := rational F G (γ j) * x
  have hmul (j : J) : H (rational F G (γ j)) ≤ H (y j) * H x := by
    have hh := adelicHeight_mul_le F G rho hN (y j) x⁻¹
    simpa only [y, mul_inv_cancel_right, adelicHeight_inv] using hh
  have hx n' : 0 < H x ^ n' := pow_pos (hpos x) _
  let D := C ^ (d + n) * B * (H x ^ n)⁻¹
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (pow_nonneg hC₀ _) hB) (inv_nonneg.mpr (hx n).le)
  have hpoint (j : J) : ‖b j‖ ≤ D * w (γ j) := by
    have hprod : H (rational F G (γ j)) ^ d * H x ^ n ≤
        C ^ (d + n) * H (y j) ^ (d + (d + n)) := by
      calc
        _ ≤ (H (y j) * H x) ^ d * H x ^ n := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (hpos _).le (hmul j) _) (hx n).le
        _ = H (y j) ^ d * H x ^ (d + n) := by rw [mul_pow, pow_add, mul_assoc]
        _ ≤ H (y j) ^ d * (C * H (y j)) ^ (d + n) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos _).le (hmin j) _) (pow_nonneg (hpos _).le _)
        _ = _ := by
          simp only [mul_pow, pow_add]
          ring
    have hweighted : ‖b j‖ * (H (rational F G (γ j)) ^ d * H x ^ n) ≤ C ^ (d + n) * B := by
      calc
        _ ≤ ‖b j‖ * (C ^ (d + n) * H (y j) ^ (d + (d + n))) :=
          mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
        _ = C ^ (d + n) * (‖b j‖ * H (y j) ^ (d + (d + n))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hbound j) (pow_nonneg hC₀ _)
    have hp : 0 < H (rational F G (γ j)) ^ d * H x ^ n :=
      mul_pos (pow_pos (hpos _) _) (hx n)
    simpa only [D, w, div_eq_mul_inv, mul_inv_rev, mul_assoc] using
      (le_div_iff₀ hp).mpr hweighted
  have hmajorant : Summable (fun j => D * w (γ j)) := (hd.comp_injective γ.injective).mul_left D
  have hnorm : Summable (fun j => ‖b j‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint hmajorant
  have hsubsum : ∑' j, w (γ j) ≤ S := tsum_comp_le_tsum_of_inj hd hwn γ.injective
  refine ⟨hnorm, ?_⟩
  have htsum : ‖∑' j, b j‖ ≤ D * S := by
    refine (norm_tsum_le_tsum_norm hnorm).trans ((hnorm.tsum_le_tsum hpoint hmajorant).trans ?_)
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hsubsum hD
  calc
    _ ≤ (D * S) * H x ^ n := mul_le_mul_of_nonneg_right htsum (hx n).le
    _ = _ := by
      dsimp only [D]
      field_simp [(hx n).ne']

end Langlands.Global.ArthurTruncation
