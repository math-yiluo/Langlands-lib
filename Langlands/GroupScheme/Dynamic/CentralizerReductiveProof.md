# Connected reductivity of actual dynamic centralizers

Authors: Workers 1325 and 1326.

`Langlands.GroupScheme.dynamicCentralizerReductive` proves exactly
`Langlands.GroupScheme.DynamicCentralizerReductiveStatement.{u}` at arbitrary
universe `u`. For every field `k`, connected reductive group scheme `G` over
`Spec k`, cocharacter `χ : Gm → G`, and supplied closed representative
`j : M → G` of `Dynamic.centralizer χ`, it proves `IsConnectedReductive M`.
The cocharacter may be trivial. There are no further structural, splitness,
perfectness, characteristic or maximal-torus hypotheses. All representation,
containment and normality predicates use the existing subgroup functors on
every test scheme.

## Radical vanishing over an algebraically closed field

The reusable lemma
`Dynamic.hasTrivialUnipotentRadical_of_borel_envelope` explicitly takes the
Chevalley envelope and centralizer Borel-containment statements as arguments.
Let `i : U → M` be any smooth connected normal unipotent closed subgroup of
the supplied centralizer. The composite `i ≫ j` is a closed inclusion into
`G`. For a maximal torus containing `χ`, the Borel-containment statement
puts its range in every Borel containing that torus. The envelope statement
then contains this range in the range of a smooth connected normal
unipotent closed subgroup `n : N → G`.

The trivial ambient unipotent radical makes the range of `n` trivial.
Range containment makes the range of `i ≫ j` trivial on every test scheme.
The representing inclusion `j` is monic, so
`SubgroupFunctor.range_comp_eq_bot_iff` cancels it and makes the range of `i`
trivial in `M`. The proof uses normality of `N` in `G`; it never infers
normality in `G` from normality in `M`.

## Scalar extension and the maximal torus

`Dynamic.isConnectedReductive_of_borel_envelope` also takes the two
structural statements explicitly. The published `dynamicSmooth` and
`dynamicConnected` prove smoothness and connectedness of the supplied
centralizer. Closedness in the affine ambient group gives affineness.
The geometric radical is checked after base change to `AlgebraicClosure k`.
The published geometric connectedness theorem gives connectedness of the
ambient group there; smoothness and affineness survive base change.
The centralizer representation and closedness also survive base change.
The radical lemma applies to this actual scalar-extended representative,
given a maximal torus containing the scalar-extended cocharacter.

Three private adapters obtain this torus from finite Galois splitting.
Finite dimensionality makes the splitting extension algebraic; over an
algebraically closed field the published split descent theorem therefore
makes each torus split. A maximal split torus is consequently maximal among
all tori. The published `cocharacterMaximalSplitTorus` supplies a maximal
split torus and an actual factorization of the cocharacter through it,
including for the trivial cocharacter. `SubgroupFunctor.range_le_of_factor`
turns this factorization into the needed all-test range containment.

## Final theorem and provenance

The final theorem supplies all of these inputs with the published proofs
`chevalleyUnipotentEnvelope`, `centralizerUnipotentBorelContainment`, and
`torusFiniteGaloisSplitting`. It applies the scalar-extension lemma to the
original arbitrary field, group, cocharacter and supplied representative,
and obtains the maximal-torus witness through the private adapters.
Its type is the unchanged named target proposition; none of the auxiliary
lemmas' explicit structural inputs remains a hypothesis of the theorem.

This module is an internal composition of published Library constructions
and theorems. The paired target statement documents the original
mathematical provenance. The implemented proof follows the normal-unipotent
envelope route described above, using the published envelope and Borel
proofs for the geometric argument. The target and its imported definitions
are unchanged, and no preferred centralizer representative is constructed.
Worker 1325 developed the radical and scalar-extension assembly; Worker 1326
contributed its connectedness integration and torus-splitting coordination.
The imported published proofs retain their own authorship.

The algebraically closed splitting adapter reuses the published
`IsTorus.isSplitTorus_of_finiteGaloisSplitting` in `Torus/SplitReflection`.
