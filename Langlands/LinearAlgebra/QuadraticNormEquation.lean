import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Norm.Transitivity

/-! # Coordinate norm equations in quadratic algebras -/

noncomputable section

namespace Langlands.QuadraticNormEquation

variable {K : Type*} [Field K]

/-- The basis `1, ω` of the quadratic algebra has two elements. -/
theorem finrank_quadraticAlgebra (a : K) : Module.finrank K (QuadraticAlgebra K a 0) = 2 := by
  rw [Module.finrank_eq_card_basis (QuadraticAlgebra.basis a 0), Fintype.card_fin]

/-- The distinguished generator of the quadratic algebra squares to the radicand. -/
theorem omega_sq (a : K) :
    (QuadraticAlgebra.omega : QuadraticAlgebra K a 0) ^ 2 =
      algebraMap K (QuadraticAlgebra K a 0) a := by
  rw [QuadraticAlgebra.omega_pow_two_eq_add, zero_smul, add_zero,
    Algebra.algebraMap_eq_smul_one]

/-- The determinant norm is `x² - a y²` in the basis `1, ω`. -/
theorem algebraNorm (a : K) (z : QuadraticAlgebra K a 0) :
    Algebra.norm K z = z.re ^ 2 - a * z.im ^ 2 := by
  rw [Algebra.norm_apply]
  change (DistribSMul.toLinearMap K (QuadraticAlgebra K a 0) z).det = _
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm, QuadraticAlgebra.norm_def]
  ring

/-- A root of a nonsquare radicand identifies a degree-two extension with its quadratic algebra. -/
def algEquivOfRoot {a : K} [Fact (¬ IsSquare a)] {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] (hL : Module.finrank K L = 2) {r : L}
    (hr : r ^ 2 = algebraMap K L a) : QuadraticAlgebra K a 0 ≃ₐ[K] L := by
  let f : QuadraticAlgebra K a 0 →ₐ[K] L := QuadraticAlgebra.lift ⟨r, by
    rw [← pow_two, hr, zero_smul, add_zero, Algebra.algebraMap_eq_smul_one]⟩
  exact AlgEquiv.ofBijective f ⟨f.injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      ((finrank_quadraticAlgebra a).trans hL.symm) (f := f.toLinearMap)).mp f.injective⟩

/-- Every scalar is represented by `x² - a y²` when `a` is a nonzero square. -/
theorem exists_eq_of_isSquare [CharZero K] {a b : K} (ha : a ≠ 0) (hs : IsSquare a) :
    ∃ x y : K, x ^ 2 - a * y ^ 2 = b := by
  obtain ⟨s, hs⟩ := hs.exists_sq
  have hs0 : s ≠ 0 := by
    intro h
    exact ha (by simpa [h] using hs)
  refine ⟨(b + 1) / 2, (b - 1) / (2 * s), ?_⟩
  rw [hs]
  field_simp
  ring

/-- A nontrivial zero of the binary form `x² - a y²` makes `a` a square. -/
theorem isSquare_of_binary_zero {a x y : K} (hne : x ≠ 0 ∨ y ≠ 0)
    (h : x ^ 2 - a * y ^ 2 = 0) : IsSquare a := by
  have hy : y ≠ 0 := by
    intro hy
    have hx : x ^ 2 = 0 := by simpa [hy] using h
    simp [eq_zero_of_pow_eq_zero hx, hy] at hne
  refine (isSquare_iff_exists_sq a).2 ⟨x / y, ?_⟩
  rw [div_pow, eq_div_iff (pow_ne_zero 2 hy)]
  exact (sub_eq_zero.mp h).symm

/-- A nontrivial zero of `x² - a y² - b z²` gives a representation of `b` by the binary norm form. -/
theorem exists_eq_of_ternary_zero [CharZero K] {a b x y z : K} (ha : a ≠ 0)
    (hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) (h : x ^ 2 - a * y ^ 2 = b * z ^ 2) :
    ∃ X Y : K, X ^ 2 - a * Y ^ 2 = b := by
  by_cases hz : z = 0
  · exact exists_eq_of_isSquare ha (isSquare_of_binary_zero (by simpa [hz] using hne)
      (by simpa [hz] using h))
  refine ⟨x / z, y / z, ?_⟩
  rw [div_pow, div_pow, ← mul_div_assoc, ← sub_div, h, mul_div_cancel_right₀ _ (pow_ne_zero 2 hz)]

end Langlands.QuadraticNormEquation
