# Openness of the stalk-frame locus of a line-bundle section

`Langlands.SchemeModule.LineBundleStalkFrameOpen` is a proposition for every
scheme `X : Scheme.{u}`, every actual locally free rank-one module sheaf
`L : LineBundle X`, and every global section `s` of `L.obj`. It asserts that
the set where `sectionHom L.obj s` induces an isomorphism of underlying
abelian-group stalks is open, and that this entire set is the underlying
set of `trivializationOpen L.obj s`. No quasi-compactness, separation, or
restriction on the base is imposed.

This is a derived prerequisite for the existing
`LineBundleSectionResidueComparison`. The general-module
`TrivializationOpenInterior` statement only identifies the interior of the
stalk-frame locus. The present statement isolates the extra consequence of
local rank one that makes this the whole locus. It does not compare the
stalk condition to the section on a residue-field pullback. That comparison
is the separate `LineBundleResidueStalkCriterion`, proved by
`Langlands.SchemeModule.lineBundleResidueStalkCriterion` in module
`Langlands.AlgebraicGeometry.Modules.SectionResidueStalkProof`.

The source motivation is the openness and local-trivialization argument in
Stacks Project Lemma 17.25.10, tag [01CY](https://stacks.math.columbia.edu/tag/01CY),
statement and proof. The retained source is
`stacks-invertible-picard-ampleness-2026-10-21`, directory SHA256
`2a0bbd01484fc7cef97110a88cf4b3e472574fbbb9469d037170744a1462f835`,
file `01CY.html`. The source starts with the germ outside the maximal ideal
times the module, obtains a stalk basis, and extends its inverse over a
neighborhood. This target isolates the portion starting from a stalk basis,
using the Library's existing actual module and stalk constructions. It
asserts neither the residue-field comparison nor construction of an inverse
bundle section. It is a proposition definition, not an axiom. A separate
module proves it: `Langlands.SchemeModule.lineBundleStalkFrameOpen :
LineBundleStalkFrameOpen.{u}` in
`Langlands.AlgebraicGeometry.Modules.LineBundleFrameOpen`.
