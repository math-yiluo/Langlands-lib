# Restriction and inflation on actual idele cohomology

This module defines restriction and inflation on the ordinary cohomology of
the published idele representation. All fields lie in an arbitrary common
universe. Restriction keeps the coefficient idele group and restricts the
acting automorphisms. Inflation restricts automorphisms from the upper field
and pushes coefficients through the actual idele inclusion. The normality
and scalar-tower hypotheses needed for these automorphism maps remain
explicit; neither a global invariant nor an arithmetic vanishing theorem is
assumed.

The maps `relativeIdeleRestriction` and `relativeIdeleInflation` commute
with both the principal embedding from field-unit cohomology and the
quotient map to idele-class cohomology, in every natural-number degree.
Restriction and inflation are each transitive and commute with each other
in the indicated scalar towers. As a direct consequence, inflation sends
the range of the idele quotient cohomology map into the corresponding range
over the upper field. This is preservation of representability by ideles,
not a claim that the quotient cohomology map is surjective.

The construction is an internal derivation from `IdeleCoefficientSequence`,
`CohomologyMaps`, `CohomologyTowerProof`, and Mathlib's functorial maps on
group cohomology. The idele inclusion is equivariant because the published
adele inclusion intertwines compatible field automorphisms. The principal
square uses `ideleInclusion_diagonal`; the quotient square is the defining
formula of the idele-class inclusion. Mathlib's composition and congruence
lemmas transport these coefficient identities to every cohomology degree.
Transitivity uses the existing tower identities for automorphism restriction
and actual adele inclusion. The range-preservation theorem inflates a
chosen idele preimage and applies the quotient square.

This supplies tower maps for the construction of global invariants. It
does not prove that total invariants are preserved by inflation or scaled
by restriction, that every idele-class cohomology class becomes represented
by ideles in a larger field, or `GlobalInvariantStatement`.
