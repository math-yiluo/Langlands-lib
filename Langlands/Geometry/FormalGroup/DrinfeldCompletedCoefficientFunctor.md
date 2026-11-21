# Drinfeld and Deligne classes on completed-unramified Nilp tests

`Nilp.completedNilpRestriction` views an algebra over the actual completed
unramified integers as an algebra over the original integer ring. The
structural map of each test supplies a unique residue coordinate, which is
preserved under morphisms of tests.

`DrinfeldFramedAtlas.completedDrinfeldClassFunctor` uses the actual classes
of framed triples whose residue map is this structural residue coordinate.
`completedDeligneClassFunctor` uses the actual admissible Deligne class functor
on the restricted coefficient algebra. Both constructions act by the existing
base change on classes.

`completedComparisonOfResidue` transfers a residue-preserving comparison to
these two functors. It projects to the Deligne coordinate in one direction.
Its inverse first adjoins the structural residue coordinate and then applies
the inverse of the supplied comparison. The inverse identities and naturality
follow from the original comparison and preservation of the residue map.

These are the completed-coefficient point functors in Drinfeld, *Coverings of
p-adic symmetric regions* (1976), §2A, printed p. 109 (PDF p. 3). The transfer
uses the underlying comparison target with its exact residue identity.
