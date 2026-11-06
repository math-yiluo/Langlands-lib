import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # The monomial basis of binary homogeneous polynomials of fixed degree -/

noncomputable section

universe v

namespace Langlands.GroupScheme.HomogeneousPolynomial

open MvPolynomial

variable {R : Type v} [CommSemiring R]

/-- The exponent of the binary monomial `X 0 ^ c * X 1 ^ (m - c)`. -/
def binaryExponent (m : ℕ) (c : Fin (m + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 c.val + Finsupp.single 1 (m - c.val)

@[simp]
theorem binaryExponent_apply_zero (m : ℕ) (c : Fin (m + 1)) :
    binaryExponent m c 0 = c.val := by
  simp [binaryExponent]

@[simp]
theorem binaryExponent_apply_one (m : ℕ) (c : Fin (m + 1)) :
    binaryExponent m c 1 = m - c.val := by
  simp [binaryExponent]

theorem degree_binaryExponent (m : ℕ) (c : Fin (m + 1)) :
    (binaryExponent m c).degree = m := by
  have hc := c.isLt
  simp only [binaryExponent, map_add, Finsupp.degree_single]
  omega

theorem binaryExponent_injective (m : ℕ) : Function.Injective (binaryExponent m) := by
  intro c c' h
  exact Fin.ext (by simpa using congrArg (fun d => d 0) h)

/-- The binary exponents of degree `m` are indexed by `Fin (m + 1)`. -/
def binaryExponentEquiv (m : ℕ) :
    Fin (m + 1) ≃ {d : Fin 2 →₀ ℕ | d.degree = m} where
  toFun c := ⟨binaryExponent m c, degree_binaryExponent m c⟩
  invFun d := ⟨d.1 0, by
    have h := Finsupp.le_degree 0 d.1
    rw [d.2] at h
    omega⟩
  left_inv c := Fin.ext (binaryExponent_apply_zero m c)
  right_inv d := by
    obtain ⟨d, hd⟩ := d
    have hsum : d 0 + d 1 = m := by
      simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hd
    refine Subtype.ext (Finsupp.ext fun i => ?_)
    fin_cases i
    · simp
    · simp only [Fin.mk_one, binaryExponent_apply_one]
      omega

/-- The monomial basis of the binary homogeneous polynomials of degree `m`, indexed by
`Fin (m + 1)`; its `c`-th vector is `X 0 ^ c * X 1 ^ (m - c)`. -/
def binaryBasis (m : ℕ) :
    Module.Basis (Fin (m + 1)) R (homogeneousSubmodule (Fin 2) R m) :=
  ((basisRestrictSupport R {d : Fin 2 →₀ ℕ | d.degree = m}).map
    (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported (Fin 2) R m).symm)).reindex
    (binaryExponentEquiv m).symm

/-- Coefficient extraction: the `c`-th coordinate of a homogeneous polynomial is its
coefficient of `X 0 ^ c * X 1 ^ (m - c)`. -/
theorem binaryBasis_repr_apply (m : ℕ) (p : homogeneousSubmodule (Fin 2) R m)
    (c : Fin (m + 1)) :
    (binaryBasis m).repr p c = (p : MvPolynomial (Fin 2) R).coeff (binaryExponent m c) :=
  rfl

theorem binaryBasis_apply_eq_monomial (m : ℕ) (c : Fin (m + 1)) :
    (binaryBasis (R := R) m c : MvPolynomial (Fin 2) R) = monomial (binaryExponent m c) 1 := by
  have hmem : monomial (binaryExponent m c) (1 : R) ∈ homogeneousSubmodule (Fin 2) R m :=
    isHomogeneous_monomial _ (degree_binaryExponent m c)
  have h : binaryBasis m c = (⟨_, hmem⟩ : homogeneousSubmodule (Fin 2) R m) := by
    rw [Module.Basis.apply_eq_iff]
    ext c'
    rw [binaryBasis_repr_apply, coeff_monomial, Finsupp.single_apply]
    by_cases hc : c = c'
    · simp [hc]
    · rw [ite_eq_right (fun h => hc (binaryExponent_injective m h)), ite_eq_right hc]
  exact congrArg Subtype.val h

/-- The `c`-th basis vector is the monomial `X 0 ^ c * X 1 ^ (m - c)`. -/
theorem binaryBasis_apply (m : ℕ) (c : Fin (m + 1)) :
    (binaryBasis (R := R) m c : MvPolynomial (Fin 2) R) = X 0 ^ c.val * X 1 ^ (m - c.val) := by
  rw [binaryBasis_apply_eq_monomial, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial,
    one_mul, binaryExponent]

theorem coeff_binaryBasis (m : ℕ) (c : Fin (m + 1)) (d : Fin 2 →₀ ℕ) :
    (binaryBasis (R := R) m c : MvPolynomial (Fin 2) R).coeff d =
      if binaryExponent m c = d then 1 else 0 := by
  rw [binaryBasis_apply_eq_monomial, coeff_monomial]

/-- Evaluation of a basis vector in any commutative `R`-algebra. -/
theorem aeval_binaryBasis {S : Type*} [CommSemiring S] [Algebra R S] (m : ℕ)
    (c : Fin (m + 1)) (x : Fin 2 → S) :
    aeval x (binaryBasis (R := R) m c : MvPolynomial (Fin 2) R) = x 0 ^ c.val * x 1 ^ (m - c.val) := by
  rw [binaryBasis_apply, map_mul, map_pow, map_pow, aeval_X, aeval_X]

/-- Evaluation of a basis vector at a point with coordinates in `R`. -/
theorem eval_binaryBasis (m : ℕ) (c : Fin (m + 1)) (x : Fin 2 → R) :
    eval x (binaryBasis (R := R) m c : MvPolynomial (Fin 2) R) = x 0 ^ c.val * x 1 ^ (m - c.val) := by
  rw [binaryBasis_apply, map_mul, map_pow, map_pow, eval_X, eval_X]

/-- Every binary homogeneous polynomial of degree `m` is the sum of its monomials
`X 0 ^ c * X 1 ^ (m - c)` with their coefficients. -/
theorem eq_sum_binaryBasis (m : ℕ) (p : homogeneousSubmodule (Fin 2) R m) :
    (p : MvPolynomial (Fin 2) R) =
      ∑ c : Fin (m + 1),
        C ((p : MvPolynomial (Fin 2) R).coeff (binaryExponent m c)) *
          (X 0 ^ c.val * X 1 ^ (m - c.val)) := by
  conv_lhs => rw [← (binaryBasis m).sum_repr p]
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Submodule.coe_smul, binaryBasis_repr_apply, binaryBasis_apply, smul_eq_C_mul]

end Langlands.GroupScheme.HomogeneousPolynomial
