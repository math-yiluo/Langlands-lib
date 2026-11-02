# Restriction of invertible projective coordinate changes

For any homomorphism of commutative rings `φ : K →+* R`,
`ProjectiveSpace.coordinateBaseChange n φ` maps an invertible coordinate
linear map over `K` to an invertible coordinate linear map over `R`.
Its matrix coefficients are exactly the images by `φ` of the original
coefficients, in the convention `e(e_j)_i`. This construction requires
neither injectivity nor flatness of `φ`.

The construction preserves identity, composition of coordinate maps,
and inverses. Changing coefficients by an identity ring homomorphism
recovers the original map, and successive coefficient changes agree
with change by the composite ring homomorphism.

The resulting actual polynomial projective scheme actions commute
with the coefficient map. Over any scheme with compatible maps to the
two coefficient spectra, the actual relative actions agree. The same
comparison commutes with a simultaneous scheme-base morphism. Here
the new coordinate equivalence is constructed; the hypotheses only
specify the original equivalence and compatibility of the base maps.

This is internal derived infrastructure. The construction transports
Mathlib's homomorphism on general linear matrix groups through the
matrix-to-linear-map and unit-to-linear-equivalence isomorphisms.
Evaluation on basis vectors gives the coefficient formula. Matrix
group functoriality and basis-vector extensionality prove the laws.
The actual scheme comparisons apply the coefficient-compatibility
results of `LinearActionBaseChange` to this coefficient formula.
No new external source assertion is used. This unit does not construct
a projective bundle or a moduli scheme.
