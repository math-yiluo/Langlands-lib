# Finite numerators in the dominant-rank coefficient assembly

This internal deduction uses `TwoBlockDominantClearedAssembly` and the published
`bilateralLaurentClearing` theorem. All coefficient equations and one-sided
support bounds are explicit premises. It supplies neither analytic identities
for actual JPSS sections nor either final dominant-rank theorem.

`bilateralReflection_upperSupport` and `bilateralReflection_lowerSupport`
change a support bound at `N` into the opposite bound at `-N`. The proof
evaluates the reflected coefficient and uses the original bound at `-n`.
The two equivalences follow by reflecting a second time.
`bilateralReflection_ofLaurentPolynomial` proves that the finite and bilateral
reflection maps agree on the coefficient embedding. The reflection fixes the
coefficient series of one, and the previously proved Laurent-action transport
then gives the assertion for every Laurent polynomial.

`existsUnique_reflectedClearedNumerator` assumes lower support bounds on `a`
and `aD` and an equation
`A • a = reflection(B) • reflection(aD)`. Reflection gives an upper support
bound on the second series. The existing bilateral clearing theorem therefore
extracts a finite Laurent polynomial `R` with coefficient series `A • a`.
Reflecting its other coefficient identity gives
`coefficients(reflection(R)) = B • aD`. Injectivity of the coefficient
embedding proves uniqueness. Neither `A` nor `B` is cancelled.
`reflectedClearedNumerator` chooses this unique polynomial;
`reflectedClearedNumerator_spec` records both identities.

`clearedProductMultiplierUnit` represents the multiplier
`c₁ c₂⁻¹ q^d₂ X^(d₁+d₂)` as a unit of the Laurent polynomial ring.
Its constant factor comes from the complex unit `c₁ c₂⁻¹ q^d₂`;
its variable factor is the existing Laurent monomial unit.
The coercion theorem identifies it with `clearedProductMultiplier`.

`existsUnique_reflectedClearedNumerator_of_unit` assumes the equation with
an additional supplied Laurent unit `M` multiplying `A`. It applies the
inverse unit to that equation, then uses the preceding numerator extraction.
The original numerator is cleared by `A`; its reflected numerator has
coefficient series `reflection(M⁻¹) * B • aD`. Only the proved unit is removed.

`twoBlock_cleared_numerators` applies that construction to the two supplied
polynomial-cleared block equations and the lower Fourier coefficient law.
It obtains the numerator of `(P₁ * P₂).toLaurent • a`. Its reflected numerator
is the coefficient series of the dual polynomial product acting on `aD`,
multiplied by the reflected inverse of the explicit whole-pair unit.
Both original polynomials and both dual polynomials remain in the conclusion.
The proof uses `twoBlock_monomial_cleared_comp` and the unit coercion law.

No common support bound in a parameter family, coefficient uniqueness from
spectral values, identification with rational zeta integrals, or polynomial
divisibility is asserted. Those analytic and comparison steps remain necessary
for the parent proof.
