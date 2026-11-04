# Actual split-unipotent contracting subgroups

Author: Worker 1478.

This internal construction combines the published dynamic-subgroup and
torus-action proofs to supply actual split-unipotent contracting-subgroup
data. It works over every field `k : Type u`, at arbitrary universe `u`,
without any characteristic, perfectness or field-size restriction.

For a smooth affine actual group scheme `G`, a cocharacter `χ` and any supplied
closed representative `j : H → G` of the full dynamic contracting subgroup
`Dynamic.unipotent χ`, `Dynamic.isUnipotent_of_isRepresentedBy_unipotent`
proves that `H` is unipotent. It specializes the existing
`isUnipotent_of_torusActionUnipotence` with the already proved
`RelativeRoot.torusActionUnipotence`. No general unipotence assertion remains
an assumption of the new theorem.

`Dynamic.isSplitUnipotent_of_isRepresentedBy_unipotent` proves the published
finite normal Ga-series property for the same `H`. Closedness in the affine
ambient group makes `H` affine. The existing dynamic smoothness and
connectedness proofs apply to this representative. Its actual cocharacter
conjugation action has zero zero-weight Lie space by the existing
`actionWeightSpace_unipotentConjugationAction_zero`. The already proved
`RelativeRoot.torusActionSplitUnipotence` therefore applies, with the
preceding unipotence proof, and supplies the split series. Ambient
connectedness is not required.

For an arbitrary actual multiplicative-group action `a` on a smooth affine
group scheme `G`, `AutomorphicAction.SplitContractingSubgroup a` records an
actual group scheme, an actual closed inclusion into the original `G`, its
representation of `a.unipotent` on every relative scheme test, and proofs
of smoothness, connectedness, unipotence and split unipotence.
`AutomorphicAction.splitContractingSubgroup` fills this package with the
existing affine representative. That representative is the dynamic
contracting subgroup of the canonical cocharacter in the actual semidirect
product. The existing factored inclusion lands in the original normal
factor `G` and represents the original action's full identity-limit functor.
Smoothness of `Gm` and its affineness supply the semidirect ambient hypotheses.
The preceding conjugation results supply unipotence and split unipotence of
this same actual representative. The range lemma exposes its exact
subgroup-functor equality.

The interpretation retains arbitrary relative tests, including nonaffine
and nonreduced schemes. The splitness conclusion uses actual smooth connected
intermediate subgroups, natural one-dimensional vector coordinates and
represented fppf successive quotients, as in the existing
`RelativeRoot.IsSplitUnipotent` predicate. No series of rational-point
subgroups is substituted.

The provenance is internal: these are direct specializations and data
packaging of the published dynamic representation, geometry, action and
weight interfaces and the two independently proved torus-action structural
statements. The unit does not prove wound-group rigidity, split-radical
product replacement, or rational lifting for pseudo-parabolic quotients.
