# Steinberg big-cell assembly from root and coroot inputs

Author: Worker 1369.

This derived assembly applies the published dominant highest-weight
existence theorem to the existing Steinberg big-cell construction. Exactly
two global inputs remain explicit:
`RootDatumExistenceStatement.{u}` and
`SplitSimplyConnectedCorootSpanStatement.{u}`. This file does not prove
either input or the unconditional `SteinbergBigCellStatement.{u}`.

`steinbergBigCellDataOfRootAndCoroot` constructs the existing complete
`SteinbergBigCellData G` for an actual affine simply connected group over
an algebraically closed field in arbitrary universe `u`, with a supplied
prime characteristic. It applies `steinbergBigCellDataOfStructuralInputs`
to the two structural inputs and the proved theorem
`splitDominantHighestWeightRepresentationsExist` from
`Rational.DominantHighestWeightProof`.

That imported theorem proves the exact global highest-weight existence
proposition for every supplied split pinning and every integral dominant
character, without a simply connectedness or coroot-span premise. The
structural assembly already supplies the proved full-space height
irreducibility theorem. Thus neither highest-weight existence nor
Steinberg height irreducibility remains an additional global premise
of this constructor.

The result retains the original group's subgroup data, all six geometric
laws on arbitrary relative test schemes, and the seventh law on cofinal
positive heights with bases of the entire specified covariant spaces.
There is no change to the subgroup inclusion, the weight coordinate,
or the quantifiers on relative tests.

`steinbergBigCell_of_rootAndCoroot` makes the same substitution in
`steinbergBigCell_of_structuralInputs`. Its conclusion is exactly the
unchanged `SteinbergBigCellStatement.{u}` under the two displayed global
antecedents.

The provenance is internal composition of the imported proofs and
constructors; no new source assertion is introduced. The unconditional
host still requires published proofs of the two structural inputs and
a final proof of the exact target.
