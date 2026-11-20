import Langlands.Representation.Archimedean.RealStandardEllipticCartanWindow

/-! # Normalization of the full elliptic Cartan window sum -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealStandardEllipticCartan

open RealBlockFourierFinite RealBlockPropagation

/-- The angular denominator for one complex coordinate. -/
def angularFactor (θ : ℝ) : ℂ := expMode 1 θ - expMode (-1) θ

theorem angularFactor_eq_sin (θ : ℝ) : angularFactor θ = 2 * Complex.I * (Real.sin θ : ℂ) := by
  have hp : expMode 1 θ = Complex.exp ((θ : ℂ) * Complex.I) := by simp [expMode]
  have hm : expMode (-1) θ = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
    unfold expMode
    congr 1
    push_cast
    ring
  rw [angularFactor, hp, hm, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,
    Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

/-- The common product of the angular denominators on the complex slots. -/
def angularProduct {r s : ℕ} (x : Coordinates r s) : ℂ :=
  ∏ i, angularFactor (x.1 i).toAdd.2

theorem angularProduct_ne_zero {r s : ℕ} {x : Coordinates r s}
    (hx : ∀ i, Real.sin (x.1 i).toAdd.2 ≠ 0) : angularProduct x ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  rw [angularFactor_eq_sin]
  exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr (hx i))

/-- The radial and parity-window factors summed over the complex and real slot assignments. -/
def cartanWindowSum {r s : ℕ} (p : Parameters r s) (x : Coordinates r s) : ℂ :=
  ∑ π : Equiv.Perm (Fin r), ∑ σ : Equiv.Perm (Fin s),
    (∏ i, Complex.exp (((x.1 i).toAdd.1 : ℂ) * (2 * (p.1 (π i)).2)) *
      ∑ j ∈ window (p.1 (π i)).1.natAbs, expMode j (x.1 i).toAdd.2) *
    ∏ j, realTerm (p.2 (σ j)) (x.2 j)

theorem angularProduct_mul_cartanWindowSum {r s : ℕ} (p : Parameters r s)
    (hp : ∀ i, 0 < (p.1 i).1) (x : Coordinates r s) :
    angularProduct x * cartanWindowSum p x = numerator p x := by
  rw [cartanWindowSum, numerator_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [angularProduct, ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have he : (((p.1 (π i)).1.natAbs : ℕ) : ℤ) = (p.1 (π i)).1 := by
    rw [Int.natCast_natAbs, abs_of_nonneg (hp (π i)).le]
  have hw := realStandardEllipticCartanWindow (p.1 (π i)).1.natAbs (p.1 (π i)).2
    (x.1 i).toAdd.1 (x.1 i).toAdd.2
  rw [he] at hw
  exact hw

/-- A common factor on the window sum becomes that factor divided by the angular product
on the finite numerator. -/
theorem mul_cartanWindowSum_eq_numerator {r s : ℕ} (p : Parameters r s)
    (hp : ∀ i, 0 < (p.1 i).1) (x : Coordinates r s)
    (hx : ∀ i, Real.sin (x.1 i).toAdd.2 ≠ 0) (C : ℂ) :
    C * cartanWindowSum p x = (C / angularProduct x) * numerator p x := by
  rw [← angularProduct_mul_cartanWindowSum p hp x, ← mul_assoc, div_mul_cancel₀ _
    (angularProduct_ne_zero hx)]

/-- The finite window sum normalizes to the Cartan numerator by a nonzero common factor
on the regular angles. -/
def RealStandardEllipticCartanWindowNormalizationStatement : Prop :=
  ∀ (r s : ℕ) (x : Coordinates r s), (∀ i, Real.sin (x.1 i).toAdd.2 ≠ 0) →
    angularProduct x ≠ 0 ∧
    ∀ p : Parameters r s, (∀ i, 0 < (p.1 i).1) → ∀ C : ℂ,
      C * cartanWindowSum p x = (C / angularProduct x) * numerator p x

theorem realStandardEllipticCartanWindowNormalization :
    RealStandardEllipticCartanWindowNormalizationStatement :=
  fun _ _ x hx => ⟨angularProduct_ne_zero hx,
    fun p hp C => mul_cartanWindowSum_eq_numerator p hp x hx C⟩

end Langlands.Archimedean.RealStandardEllipticCartan
