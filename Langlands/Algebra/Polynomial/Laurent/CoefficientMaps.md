# Coefficient maps and exponent substitutions of Laurent polynomials

Laurent polynomials over `A` are Mathlib's additive monoid algebra of `ℤ` over `A`, so an algebra map `φ : A →ₐ[R] B` acts on them coefficientwise through `AddMonoidAlgebra.mapAlgHom ℤ φ`. The file records how this map treats the two kinds of basic Laurent polynomials. A constant `C a` is the single term of degree `0` with coefficient `a`, so it goes to `C (φ a)` (`LaurentPolynomial.mapAlgHom_C`). A monomial `T n` is the single term of degree `n` with coefficient `1`, and `φ 1 = 1`, so it is fixed (`LaurentPolynomial.mapAlgHom_T`). Both follow from Mathlib's formula for the image of a single term.

The substitution `T ↦ Tⁿ` is Mathlib's `AddMonoidAlgebra.mapDomainAlgHom` along multiplication by `n` on the exponents. It fixes the constants (`LaurentPolynomial.mapDomainAlgHom_mulRight_comp_toAlgHom`): a constant is a single term of degree `0`, and `0 * n = 0`.

All three statements are `simp` lemmas.
