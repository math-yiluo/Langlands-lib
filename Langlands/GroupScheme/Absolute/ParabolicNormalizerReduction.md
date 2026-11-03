# All-test normalization from geometric Borel overgroups

This internal reduction combines the published all-test open-cell argument with
`ParabolicNormalizerPointsReduction`. It does not assert that its structural
hypotheses hold, and it does not prove the unconditional
`ParabolicSelfNormalizerStatement`.

`GeometricBorelOvergroupCondition i` states that for every algebraically closed
field `K : Type u` and every map `b : Spec K → Spec k`, the actual base changes
of the ambient group and the source subgroup are connected, and an ambient
Borel factors through the actual base-changed inclusion. Smoothness and
closedness of the source, and smoothness and affineness of the ambient group,
are separate assumptions. Closedness implies affineness of the source.

The exact `BorelConjugacyStatement` supplies Borel conjugacy inside each
connected smooth affine source. The exact `BorelNormalizerStatement` supplies
the ambient Borel point-normalizer equality. The previous reduction then puts
every normalizing base point in that source. The arbitrary-base-change
normalizer identity transports this to every geometric test map into the
original ambient group. An explicit isomorphism identifies the test
`Over.mk b` with the image of the identity test under `Over.map b`, so the
proof retains the original point and inclusion.

Given a multiplication open immersion from an actual left subgroup times the
source, and trivial intersection of that left subgroup with the all-test
normalizer, the published open-cell lemma proves equality of subgroup
functors on all tests. The geometric calculation is used only to contain
topological images in the open cell; lifting through the open immersion and
separating the left factor also works on nonreduced and non-affine tests.
`normalizerPointsEquivOfGeometricBorels` is the resulting multiplicative
equivalence between normalizer points and points of the original source. Its
companion composition lemma verifies the lift along the given inclusion.

All content is derived internally from the named published interfaces and
the explicitly stated hypotheses. No assertion of Borel conjugacy,
normalization, geometric connectedness, or existence of an open cell is
introduced as a theorem without its corresponding premise.
