# Compact coefficients on normal subgroup restrictions

This internal deduction concerns a normal subgroup `N` of a topological group
`G`, with the inherited topology, and an actual smooth complex representation
`A` of `G`. The ambient group and both representation carriers have independent
universes. The functionals are all smooth elements of the full algebraic dual.

`compactCoefficientVectors_restrict_ambient_stable` proves that the vectors
whose coefficients on `N` have compact support are preserved by the ambient
action. For `g : G`, the published inverse conjugation equivalence sends
`n` to `g⁻¹ * n * g`. The published restriction conjugation intertwiner is
the linear action of `g`. Pulling a smooth functional back along that
intertwiner gives a smooth functional on the conjugated restriction, and the
published group-equivalence comparison makes it smooth on the original
restriction. Naturality of matrix coefficients then expresses the new
coefficient as an old compact coefficient precomposed with the conjugation
homeomorphism, preserving compact support.

`compactRestrictionSubrepresentation` bundles this invariant submodule as
an actual ambient subrepresentation. In an irreducible ambient
representation, the presence of one nonzero vector in it makes it top.
`hasCompactSmoothDualCoefficients_restrict_of_exists_compact_vector` therefore
proves compactness of every smooth-dual coefficient of the restriction.
Finally, `hasCompactSmoothDualCoefficients_restrict_of_nonzero_map` uses the
published compactness-of-the-range theorem to obtain that vector from any
nonzero intertwiner from a representation with compact smooth-dual
coefficients.

The derivation uses the existing `TotalCompactness`, `AmbientProjector`,
group transport and smooth-dual naturality results. It requires neither
openness of `N`, admissibility, a finite decomposition of the restriction,
nor a Haar measure. This supplies a compactness propagation step for the
ambient embedding route to Renard VI.3.4. It does not assert a compact set
common to different representations at a fixed level or identify ambient
Jacquet cuspidality.
