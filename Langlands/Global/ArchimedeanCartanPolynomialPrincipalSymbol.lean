import Langlands.Global.ArchimedeanCartanPolynomialCoefficients
import Langlands.Global.ArchimedeanCartanSymbolBounds
import Mathlib.Data.Fintype.BigOperators

/-! # Principal-symbol correctness for the actual coefficient recurrence -/

noncomputable section
universe u
open scoped Classical Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

private def cartanArraySymbol {r : ℕ} (a : CartanCoordinateCoefficients K n r)
    (y : ArchimedeanMatrix K n) (ξ : ArchimedeanMatrix K n →L[ℝ] ℝ) : ℂ :=
  ∑ w : Fin r → Fin (cartanCoordinateDimension K n),
    a (Fin.last r) w y * ∏ j : Fin r, (ξ (cartanCoordinateBasis K n (w j)) : ℂ)

private theorem cartanCoordinateFunctional_sum (v : ArchimedeanMatrix K n)
    (ξ : ArchimedeanMatrix K n →L[ℝ] ℝ) :
    ∑ j : Fin (cartanCoordinateDimension K n),
      (cartanCoordinateFunctional K n j v : ℂ) * (ξ (cartanCoordinateBasis K n j) : ℂ) =
        (ξ v : ℂ) := by
  have h := congrArg ξ ((cartanCoordinateBasis K n).sum_repr v)
  have h' : ∑ j : Fin (cartanCoordinateDimension K n),
      cartanCoordinateFunctional K n j v * ξ (cartanCoordinateBasis K n j) = ξ v := by
    change ∑ j : Fin (cartanCoordinateDimension K n),
      (cartanCoordinateBasis K n).repr v j * ξ (cartanCoordinateBasis K n j) = ξ v
    simpa only [map_sum, map_smul, smul_eq_mul] using h
  exact_mod_cast h'

private theorem cartanLeftDirectionalCoefficients_top {r : ℕ}
    (a : CartanCoordinateCoefficients K n r)
    (V : ArchimedeanMatrix K n → ArchimedeanMatrix K n)
    (w : Fin (r + 1) → Fin (cartanCoordinateDimension K n)) (y : ArchimedeanMatrix K n) :
    cartanLeftDirectionalCoefficients K n a V (Fin.last (r + 1)) w y =
      a (Fin.last r) (fun j => w j.succ) y *
        (cartanCoordinateFunctional K n (w 0) (V y) : ℂ) := by
  simp only [cartanLeftDirectionalCoefficients, Fin.val_last, Nat.not_succ_le_self,
    dite_false, zero_add, cartanPrependCoefficient]
  rw [cartanCoefficientExtend_of_le K n a _ y (Nat.le_refl r)]
  rfl

private theorem cartanArraySymbol_left {r : ℕ}
    (a : CartanCoordinateCoefficients K n r)
    (V : ArchimedeanMatrix K n → ArchimedeanMatrix K n)
    (y : ArchimedeanMatrix K n) (ξ : ArchimedeanMatrix K n →L[ℝ] ℝ) :
    cartanArraySymbol K n (cartanLeftDirectionalCoefficients K n a V) y ξ =
      (ξ (V y) : ℂ) * cartanArraySymbol K n a y ξ := by
  unfold cartanArraySymbol
  simp_rw [cartanLeftDirectionalCoefficients_top]
  rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => Fin (cartanCoordinateDimension K n))).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_succ, Fin.cons_zero, Fin.prod_univ_succ]
  calc
    _ = (∑ j : Fin (cartanCoordinateDimension K n),
        (cartanCoordinateFunctional K n j (V y) : ℂ) *
          (ξ (cartanCoordinateBasis K n j) : ℂ)) *
        ∑ w : Fin r → Fin (cartanCoordinateDimension K n),
          a (Fin.last r) w y * ∏ j : Fin r, (ξ (cartanCoordinateBasis K n (w j)) : ℂ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = _ := by rw [cartanCoordinateFunctional_sum K n]

private theorem cartanArraySymbol_squareSum {r : ℕ}
    (a : CartanCoordinateCoefficients K n r)
    (y : ArchimedeanMatrix K n) (ξ : ArchimedeanMatrix K n →L[ℝ] ℝ) :
    cartanArraySymbol K n (cartanSquareSumCoefficients K n a) y ξ =
      (ambientCartanCovectorForm K n y ξ : ℂ) * cartanArraySymbol K n a y ξ := by
  calc
    _ = ∑ i : CartanBasisIndex K n,
        cartanArraySymbol K n
          (cartanLeftDirectionalCoefficients K n
            (cartanLeftDirectionalCoefficients K n a (cartanMatrixField K n i))
            (cartanMatrixField K n i)) y ξ := by
      unfold cartanArraySymbol
      simp only [cartanSquareSumCoefficients, Finset.sum_mul]
      exact Finset.sum_comm
    _ = ∑ i : CartanBasisIndex K n,
        (ξ (cartanMatrixField K n i y) : ℂ) *
          ((ξ (cartanMatrixField K n i y) : ℂ) * cartanArraySymbol K n a y ξ) := by
      simp_rw [cartanArraySymbol_left]
    _ = _ := by
      simp only [ambientCartanCovectorForm, Complex.ofReal_sum, Complex.ofReal_pow,
        Finset.sum_mul, cartanMatrixField]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The symbol of each actual Cartan iterate is the corresponding quadratic-form power. -/
private theorem cartanIterateCoefficients_principalSymbol (m : ℕ)
    (y : ArchimedeanMatrix K n) (ξ : ArchimedeanMatrix K n →L[ℝ] ℝ) :
    cartanArraySymbol K n (cartanIterateCoefficients K n m) y ξ =
      (ambientCartanCovectorForm K n y ξ : ℂ) ^ m := by
  induction m with
  | zero => simp [cartanArraySymbol, cartanIterateCoefficients, cartanIdentityCoefficients]
  | succ m ih =>
    have he : cartanArraySymbol K n (cartanIterateCoefficients K n (m + 1)) y ξ =
        cartanArraySymbol K n
          (cartanSquareSumCoefficients K n (cartanIterateCoefficients K n m)) y ξ := by
      unfold cartanArraySymbol
      simp only [cartanIterateCoefficients, Fin.val_last, Nat.mul_succ]
      apply Finset.sum_congr rfl
      intro w _
      rw [cartanCoefficientExtend_of_le K n _ _ y (by omega)]
      rfl
    rw [he, cartanArraySymbol_squareSum, ih, pow_succ]
    ring

/-- The top coefficient of a monic polynomial is the top coefficient of its highest iterate. -/
private theorem cartanPolynomialCoordinateOperator_top (p : Polynomial ℂ) (hp : p.Monic)
    (w : Fin (2 * p.natDegree) → Fin (cartanCoordinateDimension K n))
    (y : ArchimedeanMatrix K n) :
    (cartanPolynomialCoordinateOperator K n p).coefficient (Fin.last (2 * p.natDegree)) w y =
      cartanIterateCoefficients K n p.natDegree (Fin.last (2 * p.natDegree)) w y := by
  change (∑ m ∈ p.support, p.coeff m *
    cartanCoefficientExtend K n (cartanIterateCoefficients K n m) (2 * p.natDegree) w y) = _
  rw [Finset.sum_eq_single p.natDegree]
  · rw [hp.coeff_natDegree, one_mul,
      cartanCoefficientExtend_of_le K n _ _ y (Nat.le_refl _)]
    rfl
  · intro m hm hne
    have hmdeg : m ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp m hm
    rw [cartanCoefficientExtend_of_lt K n _ _ y (by omega)]
    exact mul_zero _
  · intro hnot
    exact (hnot (Polynomial.natDegree_mem_support_of_nonzero hp.ne_zero)).elim

/-- The concrete monic polynomial operator has the full predicted symbol at every ambient point. -/
theorem cartanPolynomialCoordinateOperator_principalSymbol (p : Polynomial ℂ) (hp : p.Monic)
    (y : ArchimedeanMatrix K n) (ξ : ArchimedeanMatrix K n →L[ℝ] ℝ) :
    (cartanPolynomialCoordinateOperator K n p).principalSymbol y ξ =
      (ambientCartanCovectorForm K n y ξ : ℂ) ^ p.natDegree := by
  unfold Langlands.Analysis.CoordinateScalarOperator.principalSymbol
  simp_rw [cartanPolynomialCoordinateOperator_top K n p hp]
  exact cartanIterateCoefficients_principalSymbol K n p.natDegree y ξ

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (p : Polynomial ℂ), p.Monic → ∀ (y : ArchimedeanMatrix K n)
      (ξ : ArchimedeanMatrix K n →L[ℝ] ℝ),
    (cartanPolynomialCoordinateOperator K n p).principalSymbol y ξ =
      (ambientCartanCovectorForm K n y ξ : ℂ) ^ p.natDegree :=
  @cartanPolynomialCoordinateOperator_principalSymbol

end Langlands.Global.ArchimedeanGL
