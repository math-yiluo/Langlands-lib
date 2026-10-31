# Logical assembly of cuspidal-induction association

Author: Worker 120.

This module supplies the logical assembly used by `AssociationProof`. Its
helper theorems make their analytic inputs explicit. The closing theorem in
that module supplies every input from published proofs.

The namespace `Langlands.CuspidalSupport.AssociationAssembly` defines the
proposition-valued interface `ArtinianInput F T n`, requiring Artinianness of
every target canonical normalized induction from irreducible cuspidal data.
The reverse input is the existing
`Langlands.CuspidalSupport.CuspidalInductionReverseAssociationTheorem F T n`:
a common actual irreducible subquotient of two canonical normalized inductions
implies association of their inducing data. The field and both inducing
carrier universes remain independent.

`positiveRank` takes the forward Hom theorem at the source/target and
source/source universes, association reflexivity for the source universe,
the forward factor theorem, positive rank, the local Artinian interface, and
the published reverse-association proposition.
Its conclusion is the unchanged
`CuspidalInductionAssociationTheorem F T n`.

First it applies the diagonal forward Hom input to reflexive association.
The resulting nonzero endomorphism proves that the source induction is
nontrivial: every linear map on a subsingleton carrier would be zero.
The published `nonzeroHomCommonSubquotient` converts any nonzero Hom to a
common actual irreducible subquotient, using target Artinianness.
The published `sameFactorsCommonSubquotient` converts matching factors to
a common actual irreducible subquotient, using the source nontriviality.
The reverse input then proves the reverse direction of both equivalences.
Forward Hom and its subquotient bridge prove the forward common-subquotient
direction. The forward factor direction is supplied by its explicit input.
This constructs all three equivalences in the literal host proposition.

`artinianInput_of_length` extracts target Artinianness from the group-algebra
finite-length conclusion of `CuspidalInductionLengthTheorem`, using
Mathlib's equivalence of finite length with Noetherianness and Artinianness.
`allRanks` splits the natural rank into zero and positive rank. At zero it
uses the published `cuspidalInductionAssociationRankZero`. At positive rank
it applies `positiveRank` and the Artinian adapter. Its length and reverse
inputs are needed only at positive ranks.

This is an internal logical deduction from the existing definitions and
algebraic bridge proofs. It introduces no sourced mathematical statement or
new axiom. Its explicit theorem inputs are all discharged by the closing
theorem in `AssociationProof`. The host statement and all imported pairs
are preserved unchanged.
