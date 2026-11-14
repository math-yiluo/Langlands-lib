# A global reduction for apartment-compatible unramified descent

`UnramifiedApartmentDescentReductionStatement` is the implication from six
global inputs to the exact existing proposition
`UnramifiedApartmentDescentStatement`, at an arbitrary universe parameter.
The six inputs are special-torus existence, unramified valuation descent,
apartment axioms for compatible classes, the Chapter 7 building axioms,
rational orbit representatives for fixed upper building points, and the
actual affine-root restriction statement
`UnramifiedAffineRootRestrictionStatement`.

The last premise is the separate statement of actual affine-root restriction.
It is stronger than a comparison of root directions alone and is not proved
by this reduction. Its three affine-map hypotheses are supplied for the
concrete `descentAffineMap`: coefficient fixedness by
`descentAffineMap_fixed`, restriction of each lifted point by
`descentPoint_val`, and the linear-part formula by the definition of its
quotient linear map.

`descentAffineMap_roots_of_unramifiedAffineRootRestriction` applies the
root statement in a concrete apartment context. It uses the connected
reductive witness carried by `B` and the three identities just described
to supply the root equality of the assembly.

`unramifiedApartmentDescentReduction` proves the stated implication.
Starting with the arbitrary lower datum `B`, it chooses the upper torus
using special-torus existence. The published
`henselianDiscreteQuasiSplit` and
`unramifiedQuasiSplit_of_henselianDiscrete` give quasi-splitness over the
actual maximal unramified field. The published
`quasiSplitIntegerApartmentExistence`, through `exists_omegaCompatible`,
then supplies an upper compatible valuation class. Reductivity under field
extension, rank-one factorization and Galois stability supply the other
structural data.

Valuation descent supplies the lower compatible class and the fixed-lift
and normalizer comparisons. Uniqueness of compatible classes identifies
that class with the apartment of the supplied `B`. The root-comparison
premise then applies to this same datum and the concrete affine map.
The existing filtration comparison, the published
`maximalUnramifiedApartmentInjective`, the apartment and Chapter 7 inputs,
and the fixed-building-point input provide the remaining arguments of
`apartmentDescentData`. Finally the proof unpacks its eight fields into
the exact existential conclusion of the original target.

This is an internal reduction derived from the named Library constructions
and their proved consequences. It introduces no new hypotheses into the
original target and edits none of its imports. It proves neither the six
remaining inputs nor the unconditional target. In particular, a separate
special-point descent premise is unnecessary here because the actual-root
comparison already supplies both facets and special-point reflection in
the eight-clause assembly.
