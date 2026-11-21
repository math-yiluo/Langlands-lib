# Translation polynomials of adelic exponents

This module supplies algebra for the passage from Bernstein–Lapid's exponent and difference equations to the monic translation polynomials of `Ξ_main`. It uses the library's `polynomialFunctions`, `StandardParabolicFamily`, and `AdelicGroupPoints.IsTranslationPolynomialSolution` conventions. The proof is an algebraic implementation, not a proof of local finiteness or of the separation of functions by their cuspidal constant-term pairings.

## Polynomials of labelled roots

`translationRootPolynomial I r` is the product of `X - C (r i)` over the finite set of labels `I`, not over the set of *values* of the roots. In particular, coincident roots retain multiplicity, and the empty product is `1`. The module proves monicity, degree `I.card`, and the product formula for the constant coefficient. It also proves weak holomorphy of every coefficient for holomorphic roots on an open subtype of complex coordinate space. The proof inducts over the label set: multiplying by a factor with root `r` changes the constant coefficient `c₀` to `-r c₀` and the coefficient `cₖ₊₁` to `cₖ - r cₖ₊₁`. No ordering or separation of the roots is used.

For fixed adelic `a`, `differentiable_parameterPower_affine` proves that `s ↦ a^(L s + μ)` is entire. Pairing `L s` with `characterLog a` is a complex linear functional on the finite-dimensional coordinate space, hence continuous. Exponentiating its sum with a constant gives the result. `isHolomorphicOn_parameterPower_affine` restricts this function to an open subtype and checks it against every continuous linear form, as required by the Library's weak holomorphy predicate.

## Polynomial action and finite differences

`isTranslationPolynomialSolution_iff_aeval` identifies the existing pointwise power sum with evaluation of a polynomial at the linear endomorphism `f(g) ↦ f(a g)`. This is `GroupAction.leftFunctions a⁻¹`, since the library representation acts on arguments by the inverse. A product of annihilators for the same translation annihilates the sum of the corresponding components: for each summand commute its annihilating factor to the right before applying the product.

On the real vector space of character logarithms, `polynomialDifference h` is the linear map `p ↦ (v ↦ p(v+h)-p(v))`. It lowers the degree bound by one and kills degree-zero functions. For a product of linear forms write it as `ℓ q`; its difference is `ℓ(v) (q(v+h)-q(v)) + ℓ(h) q(v+h)`. A translated product of `k` linear forms has degree at most `k`, as follows by induction using linearity of the first factor and closure under addition. The difference result for the spanning products extends by linearity to their complex span.

## From exponents to polynomial equations

`StandardParabolicFamily.HasPolynomialOrbit` names the degree-bounded part of `HasUnnormalizedExponent`: the bound `k` is common to all base points `g`, while the orbit polynomial `p_g` may depend on `g`. Let `T_a φ(g) = φ(a g)` for `a` in the positive split component. The operator `unnormalizedExponentDifference` is `T_a - a^λ Id`. If `x ↦ x^(-λ) φ(x g)` is `p_g(H_P(x))` on the split component, then the orbit of `(T_a - a^λ Id) φ` has polynomial

\[
 v \longmapsto a^\lambda\bigl(p_g(v + H_P(a)) - p_g(v)\bigr).
\]

This follows from commutativity in the split component, the character law for `parameterPower`, and the additivity of `characterLog`. It lowers the bound by one. At degree zero this orbit vanishes, and evaluation at `x = 1` shows `(T_a - a^λ Id) φ = 0`. Induction from the last factor of a list therefore shows that any `k + 1` differences in arbitrary split-component directions annihilate `φ`.

Repeating one direction `a` and evaluating the polynomial `(X - C (a^λ))^(k+1)` at `T_a` gives exactly `IsTranslationPolynomialSolution`, by the pointwise comparison above. For `HasExponent` the same two conclusions hold with `λ + ρ_P` in place of `λ`, since the Library's normalized action is `a^(-ρ_P) T_a` and `hasExponent_iff` identifies the two exponent conventions. The multiplicity is uniform over the directions `a` for the given exponent witness; the module does not assert a common multiplicity for an arbitrary parameter family. The sum result concerns components annihilated along the **same** shift. Transport between different parabolics, the separation argument in (8.1), and the selection of the exponents in (8.3) are not supplied here.

Source: J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §6.2 (6.2)–(6.3), §7.2 (translation polynomials), §8.1 (difference operators), and §8.4 (8.3). The polynomial construction and degree-lowering proof implement the algebra relating those formulas for the Library's actual adelic shifts.
