# Rebasing a valid corrected KP assignment

`Langlands.BruhatTits.SpecialCompact.validAssignmentTorusRebasing` proves
`ValidAssignmentTorusRebasingStatement.{u}` at arbitrary universe `u`.

For every assignment `B` with full corrected validity `B.IsValid`, every
nonarchimedean local field `F`, every connected reductive group `G` over `F`,
and every prescribed maximal split torus `i : S.toGrp → G`, the conclusion
gives an assignment `B'` with full validity, equality
`(B'.datum F G hG).base.S = S`, and heterogeneous equality
`HEq (B'.datum F G hG).base.i i`.

## Implemented proof

The proof supplies the published theorem
`Langlands.Geometry.Building.kpBuildingDatumTransportStatement` from module
`Langlands.Geometry.Building.FullValidity.DatumTransportProof` to
`rebaseAssignmentFromDatumTransport` from module
`Langlands.BruhatTits.SpecialCompact.AssignmentRebasingConstruction`.
It returns the assignment and the three properties stored in that
construction's subtype.

The construction uses `Langlands.GroupScheme.maximalSplitTorusConjugacy` to
obtain a rational inner automorphism of `G` and an isomorphism from the old
base torus to `S`. The supplied transport theorem constructs the entire new
KP datum and preserves every field of `SatisfiesGroupAxioms`, including the
integral model and quotient families. It also gives both geometric directions
of the building comparison and forward equivariance along that inner
automorphism.

`KPBuildingDatum.BuildingEquivalence.ofInner` precomposes the comparison with
source translation by the inverse rational point, producing identity
equivariance. `KPBuildingAssignment.replaceDatum_isValid` then preserves the
full assignment validity, including the cross-group and field comparisons,
when replacing the chosen datum. The exact evaluation of the replacement
gives the prescribed torus and inclusion.

## Provenance and scope

This is a derived composition of the named published results. Its only
building premise is the given `B.IsValid`; full-datum transport is discharged
by its published proof. There is no assumption that a valid assignment exists,
and no added characteristic, rank, splitness, quasi-splitness or ramification
restriction. The proof establishes the stated rebasing implication.
