import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Data.Rat.Floor

/-! # Bounded sets in a lattice with a rational positive form -/

open scoped nonZeroDivisors
open Matrix

noncomputable section

namespace Langlands

variable {L : Type*} [AddCommGroup L] [Module ℤ L]

/-- The sublevel set of the diagonal of a rational-valued integral bilinear form. -/
def rationalBilinearBall (B : L →ₗ[ℤ] L →ₗ[ℤ] ℚ) (r : ℚ) : Set L :=
  {x | B x x ≤ r}

/-- An integral basis and a strictly positive symmetric rational bilinear form
give finite bounded sets. -/
theorem finite_rational_bilinear_le_of_basis
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℤ L)
    (B : L →ₗ[ℤ] L →ₗ[ℤ] ℚ)
    (hsym : ∀ x y, B x y = B y x)
    (hpos : ∀ x : L, x ≠ 0 → 0 < B x x) (r : ℚ) :
    (rationalBilinearBall B r).Finite := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (ℤ⁰) (fun ij : ι × ι => B (b ij.1) (b ij.2))
  choose N hN using hd
  let A : Matrix ι ι ℤ := fun i j => (d : ℤ) * N (i, j)
  let c : ℚ := (d : ℤ) ^ 2
  have hc : 0 < c := by
    exact sq_pos_of_ne_zero (by exact_mod_cast nonZeroDivisors.coe_ne_zero d)
  have hcast (i j : ι) : (A i j : ℚ) = c * B (b i) (b j) := by
    have h := hN (i, j)
    change (N (i, j) : ℚ) = (d : ℤ) • B (b i) (b j) at h
    simp only [A, Int.cast_mul, h, zsmul_eq_mul, c, pow_two, mul_assoc]
  have heval (x : ι → ℤ) :
      ((x ⬝ᵥ A *ᵥ x : ℤ) : ℚ) = c * B (b.equivFun.symm x) (b.equivFun.symm x) := by
    simp only [dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul, hcast,
      Module.Basis.equivFun_symm_apply, map_sum,
      LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      zsmul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym (b j) (b i)]
    ring
  have hA : A.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · apply Matrix.IsHermitian.ext
      intro i j
      apply Int.cast_injective (α := ℚ)
      simpa only [star_trivial] using
        (hcast j i).trans ((congrArg (c * ·) (hsym (b j) (b i))).trans (hcast i j).symm)
    · intro x hx
      have hx' : b.equivFun.symm x ≠ 0 := by
        intro h
        apply hx
        exact b.equivFun.symm.injective (h.trans (map_zero _).symm)
      have hp := mul_pos hc (hpos _ hx')
      rw [← heval x] at hp
      exact_mod_cast hp
  refine Set.Finite.of_injOn (f := b.equivFun) (t := {x | x ⬝ᵥ A *ᵥ x ≤ ⌈c * r⌉})
    ?_ b.equivFun.injective.injOn (hA.finite_setOfPred_dotProduct_mulVec_le _)
  intro x hx
  change b.equivFun x ⬝ᵥ A *ᵥ b.equivFun x ≤ ⌈c * r⌉
  have h : ((b.equivFun x ⬝ᵥ A *ᵥ b.equivFun x : ℤ) : ℚ) ≤ (⌈c * r⌉ : ℤ) := by
    rw [heval, b.equivFun.symm_apply_apply]
    exact (mul_le_mul_of_nonneg_left hx hc.le).trans (Int.le_ceil _)
  exact_mod_cast h

/-- Finite free integral modules have finite bounded sets for every strictly
positive symmetric rational bilinear form. -/
theorem finite_rational_bilinear_le
    [Module.Free ℤ L] [Module.Finite ℤ L]
    (B : L →ₗ[ℤ] L →ₗ[ℤ] ℚ)
    (hsym : ∀ x y, B x y = B y x)
    (hpos : ∀ x : L, x ≠ 0 → 0 < B x x) (r : ℚ) :
    (rationalBilinearBall B r).Finite :=
  finite_rational_bilinear_le_of_basis (Module.finBasis ℤ L) B hsym hpos r

end Langlands
