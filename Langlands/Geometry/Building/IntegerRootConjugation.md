# Integer-valued opposite-root conjugation

This internal helper adapts the algebraic arguments of `MoyPrasadDoubleRefinement`,
`MoyPrasadBlockExchange` and `MoyPrasadRootConjugation` from the Library's
`ParahoricBuildingData` to `IntegerValuationBuildingData`. It is part of the
proof development for the published `LocalMoyPrasadGroupPropertiesStatement`.
It assumes an order-one unit only where the extended affine root system is
needed, through the published `IntegerValuationExtendedAffineRoots`, rather
than assuming apartment axioms. No local-field structure on the integer-valued
field is used.

The published `IntegerMoyPrasadBlockSubgroups` supplies injectivity of opposite
root/centralizer/root multiplication, commutativity of the doubled-root and
ordinary root groups, and the constant-depth block subgroup. It also supplies
`rankOne_double_positive_difference`: for an input in the doubled-root group,
the positive-coordinate difference has depth at least `2t+t'`. This module
imports those declarations rather than defining them again.

The real-depth ordinary rank-one factorization retains its
valuation-preserving centralizer factor, using the published root-rank-one
factorization and valuation exchange without a torus filtration assumption.
The mixed real-depth factorization applies the imported difference bound and
opposite-product uniqueness to retain the original doubled-root depth.

V3 bounds same-root commutators by the doubled-root filtration. To conjugate an
opposite positive-depth element by a depth-zero root element, the proof writes
the latter in an opposite reflection factor pair, uses the translation formula
for the reflection, and exchanges the resulting ordinary and doubled terms.
The resulting positive coordinate lies in the original block, while the other
two coordinates are in the opposite root group and centralizer. This is a
coordinate bound only, not yet the full Moy–Prasad membership assertion.
