# Integer-valued building comparison over an arbitrary field

This is an internal derived adapter of the published transport constructions and
the uniqueness of full integer-valued omega-compatible apartment classes. Its
source motivation is Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Proposition 6.2.6, printed p.216 / PDF p.247. The 2024 corrections, PDF p.32,
make no change to that proposition.

The comparison uses an arbitrary field `k`, an arbitrary integer-valued
valuation, and supplied `IntegerValuationBuildingData`. It imposes no local-field
structure or characteristic restriction. It does not construct those data,
building axioms, a special torus, a model, or an apartment through a prescribed
point.

## Identification of the supplied target class

`IntegerValuation.IsOmegaCompatible.transport_eq_of_isMaximalSplitTorus`
starts with full centralizer compatibility of a source class and a separately
supplied target class. The actual torus and ambient group isomorphisms must
commute with their inclusions. The target ambient group is connected reductive,
and its torus is maximal split.

Published `IntegerValuation.IsOmegaCompatible.transport_basedIso` carries full
V 6 to the target torus, with the supplied target centralizer representative.
`IntegerValuation.IsOmegaCompatible.eq_of_isMaximalSplitTorus` then identifies
the transported class with the supplied class. The latter theorem discharges
the rank-one opposite-pair condition using published rational root
factorization. Thus no matching family or common apartment point is an
additional hypothesis. The membership corollary applies to every source point.

## Actual apartment and quotient comparisons

The `IntegerValuationBuildingData.apartmentComparison` and
`buildingComparison` maps reuse
`KPApartmentData.apartmentTransportAffineEquivOfMem` and
`reducedBuildingTransportEquivOfMem` from the published
`CrossTorusApartmentComparison` and `CrossTorusBuildingComparison` modules.
An arbitrary source apartment point supplies their membership witness through
the preceding theorem. The existing comparisons are independent of that
witness.

The apartment charts commute with these maps, and the quotient comparison
intertwines the actual map on rational points of the ambient isomorphism.
The full fixers and the intersections with `characterValuationKernel` have
exactly their subgroup images. The character-kernel assertion uses published
`mem_characterValuationKernel_mapIso_iff`. The affine-root sets correspond
under the affine comparison. Expressing a special building point as a rational
translate of a special apartment point proves preservation and reflection of
special points.

## Comparison for one ambient group

`IntegerValuationBuildingSameGroupComparisonStatement` asserts that any two
supplied data for the same group and valuation admit a quotient equivalence
intertwining the identical rational-point action. At corresponding points,
the full fixers and the character-kernel stabilizers are equal as subgroups of
that same rational-point group; specialness is equivalent.

`integerValuationBuildingSameGroupComparison` proves that proposition using
published `maximalSplitTorusConjugacy` for the actual maximal split tori.
The based comparison then intertwines an inner automorphism. Composing it
with multiplication by the inverse conjugator on the target cancels the inner
twisting. Equivariance and injectivity imply equality of full fixers and
character-kernel stabilizers. Specialness is invariant under this final
rational-point translation.

This removes a comparison obstruction when independently constructed
integer-valued building data are related to supplied data, including over the
maximal unramified field. It does not prove prescribed-point containment in a
special apartment, or `UnramifiedFixedPointSplitTorusStatement`.
