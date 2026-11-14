# Reductivity of a relative Levi subgroup

This internal derived unit proves `IsRelativeLeviSubgroup.isReductive`: if
`l : L ⟶ P` is a relative Levi subgroup, `i : P ⟶ G` is a relative parabolic,
and `G` is reductive, then `L` is reductive. The base scheme and its universe
are arbitrary. No additional hypothesis on the base or the Levi is required.
`RelativeLevi.reductiveSource` retains the actual source `L` as a group scheme
equipped with this derived reductivity proof.

The field lemma `hasTrivialUnipotentRadical_of_radical_complement` starts
with an actual multiplication isomorphism `L × U ⟶ P`, a closed `L`, an affine
`P`, and a represented unipotent radical `r : U ⟶ P`. Normality of the radical
gives the published group homomorphism `leviRetraction : P ⟶ L`. Its underlying
scheme morphism is smooth by smoothness of the radical, quasi-compact because
both source and target are affine schemes over the field, and surjective
because the Levi embedding is its section. The published all-test kernel
identity identifies its represented kernel with the supplied radical range.
The smooth radical quotient theorem therefore gives trivial unipotent radical
of `L`. If `L` is smooth and `P` is connected, surjectivity of the retraction
also makes `L` connected; the companion lemma
`isPseudoReductive_of_radical_complement` packages these conclusions.

For a relative parabolic, `connectedSpace_geometricFiber` first takes its
residue-field parabolic inside the connected reductive residue fibre of `G`.
The published connectedness theorem for field parabolics makes this parabolic
connected. Smoothness and affineness allow extension to the algebraic closure.
The canonical base-change composition isomorphism identifies this extension
with the actual geometric fibre of `P`.

For the relative Levi, closedness in the affine `P` gives affineness, and
smoothness is part of its defining predicate. Its radical witness pulls back
to a represented radical on each geometric fibre by the relative radical
predicate. The actual multiplication isomorphism survives base change. The
field complement lemma then makes every geometric Levi fibre pseudo-reductive,
which is exactly the remaining clause of `IsReductive L`.

The provenance is internal: the proof combines `RelativeLevi.Basic`, the
base-change multiplication comparison in `ConjugatorUniquenessBaseChange`,
`Rational.LeviRetraction`, `Rational.CentralLeviTorusRadical`,
`Reductive.UnipotentRadicalQuotientProof`,
`Rational.ParabolicConnectedConjugacy`, `GeometricConnectedness`, and
`Reductive.BaseChange`. It asserts no new literature claim, existence of tori,
or conjugacy of relative Levi subgroups.
