# Exact affine pinned automorphisms preserve the relative local pinning

This internal bridge compares the exact `IsPinnedAutomorphism` predicate in the
affine automorphism-group statement with the relative concrete and fppf-local
pinning predicates on actual pullbacks.

The construction `IsPinnedAutomorphism.simplePermutation` is the actual
bijection of the chosen simple support induced by the supplied based label.
The local pinning proofs use this fixed bijection on every coefficient test.

An exact original simple-vector equation remains an equation on every
coefficient test by naturality of the actual differential with coefficient
change. Projection to the two pullback factors then gives equality of the
actual dual-number pinning points. The based root-index automorphism restricts
to the required bijection of simple supports. This proves
`PreservesLocalPinning` on every scheme pullback.

If the original base is nonempty, one residue-field test forces the coordinate
root datum to have the standard dot pairing. The exact character formula then
supplies a `BasedCoordinateIso` with root equivalence the inverse of the target
label, reflecting the contravariant character convention. Its canonical
cocharacter equation persists under arbitrary scheme base change. The supplied
torus square also persists under the canonical torus comparisons. These three
clauses give `IsLocallyPinned` and therefore `IsFppfLocallyPinned`.

The original base only needs nonemptiness for the pairing and cocharacter
clauses. The common pullback schemes may be disconnected, nonaffine or empty.
The module supplies a consequence of an exact pinned automorphism; it does not
construct representatives or prove the parent semidirect-product statement.
