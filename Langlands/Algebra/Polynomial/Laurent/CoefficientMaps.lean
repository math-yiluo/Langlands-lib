module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Data.Int.Cast.Lemmas

/-! # Coefficient maps and exponent substitutions of Laurent polynomials

An algebra map `φ : A →ₐ[R] B` acts on Laurent polynomials coefficientwise, through
`AddMonoidAlgebra.mapAlgHom ℤ φ`. It sends a constant `C a` to `C (φ a)` and fixes every monomial
`T n` (`LaurentPolynomial.mapAlgHom_C`, `LaurentPolynomial.mapAlgHom_T`). The substitution
`T ↦ Tⁿ`, that is `AddMonoidAlgebra.mapDomainAlgHom` along multiplication by `n` on the exponents,
fixes the constants (`LaurentPolynomial.mapDomainAlgHom_mulRight_comp_toAlgHom`).
-/

public section

namespace LaurentPolynomial

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
variable [Algebra R A] [Algebra R B]

/-- A coefficient map sends the constant Laurent polynomial `C a` to `C (φ a)`. -/
@[simp]
theorem mapAlgHom_C (φ : A →ₐ[R] B) (a : A) :
    (AddMonoidAlgebra.mapAlgHom ℤ φ) (C a) = C (φ a) := by
  rw [← single_eq_C, ← single_eq_C, AddMonoidAlgebra.mapAlgHom_single]

/-- A coefficient map fixes every Laurent monomial, since `φ 1 = 1`. -/
@[simp]
theorem mapAlgHom_T (φ : A →ₐ[R] B) (n : ℤ) :
    (AddMonoidAlgebra.mapAlgHom ℤ φ) (T n) = T n := by
  rw [T, AddMonoidAlgebra.mapAlgHom_single, map_one]
  rfl

/-- The substitution `T ↦ Tⁿ` fixes the constant Laurent polynomials: the exponent `0` of a
constant is sent to `0 * n = 0`. -/
@[simp]
theorem mapDomainAlgHom_mulRight_comp_toAlgHom {S : Type*} [CommSemiring S] [Algebra R S]
    (n : ℤ) :
    (AddMonoidAlgebra.mapDomainAlgHom R S (AddMonoidHom.mulRight n)).comp
        (IsScalarTower.toAlgHom R S (LaurentPolynomial S)) =
      IsScalarTower.toAlgHom R S (LaurentPolynomial S) := by
  ext s
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← C_eq_algebraMap, ← single_eq_C,
    AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single, map_zero]

end LaurentPolynomial
