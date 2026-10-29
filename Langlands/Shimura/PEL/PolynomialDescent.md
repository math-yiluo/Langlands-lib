# Descent of a multivariate polynomial along a coefficient embedding

This internal algebraic helper lifts a multivariate polynomial along a
commutative-ring homomorphism when each coefficient is in its range. It
uses Mathlib's existing `MvPolynomial.mem_range_map_iff_coeffs_subset`;
it does not assume or prove an arithmetic coefficient-membership theorem.

In namespace `Langlands.Shimura.PolynomialDescent`, the three coefficient
rings `R`, `S`, `T` and the variable type `ι` have independent universes.
All coefficient rings are commutative rings. The variable type need not
be finite. Given `f : R →+* S`, `p : MvPolynomial ι S`, and
`hp : ∀ d, p.coeff d ∈ Set.range f`, the private existence proof uses the
Mathlib range criterion and the fact that every occurring coefficient is
the coefficient at some monomial. `descend f p hp` chooses one preimage.
No injectivity is needed to construct it.

`map_descend` proves that applying `MvPolynomial.map f` recovers `p`.
`map_coeff_descend` applies coefficient extraction to this equality.
When `f` is injective, `unique` proves that any polynomial mapping to `p`
equals the chosen one, using injectivity of `MvPolynomial.map f`.
Thus the result does not depend on a choice of preimage in that case.

`descend_isHomogeneous` reflects homogeneity through the injective map,
and `support_descend` reflects the finite monomial support. Both use the
corresponding existing Mathlib lemmas and `map_descend`.
`eval₂_descend` states that evaluation through any further ring map
`g : S →+* T` agrees with evaluation of the original polynomial.
It follows from `MvPolynomial.eval₂_map` and `map_descend`. This last
identity does not require injectivity, a field, reducedness, or a
nonzero target ring.

The provenance is a direct derivation from the cited Mathlib interfaces.
This helper constructs no reflex field, Hodge representation, integral
coefficient theorem, Lie module or moduli scheme. Worker 57 authored it.
