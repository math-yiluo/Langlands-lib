# Cartan generation from the structural isogeny reduction

This is a derived conditional induction theorem for actual group schemes. It
retains five explicit hypotheses: `NilpotentCentralTorusStatement`,
`UnipotentSemisimpleStatement`, `CartanStructureStatement`,
`Lie.SemisimpleCentralizerSpanningStatement`, and
`SemisimpleIsogenyReductionStatement`, all at the same arbitrary universe `u`.
`CartanGenerationIsogenyInductionStatement` says that these five propositions
imply the exact published `CartanGenerationStatement.{u}`.

The conclusion applies to every infinite field, including imperfect fields,
and every smooth connected affine group over that field. Its generation
property concerns arbitrary actual closed subgroup competitors, with full
range on every test scheme. The competitors need not be smooth, reduced or
connected. The five structural inputs are hypotheses of this result; this
module does not discharge them or prove the unconditional generation target.

## Implemented proof

`isGeneratedByCartanSubgroups_of_nilpotent` uses the central maximal torus
provided by `NilpotentCentralTorusStatement`. Its centralizer is the whole
ambient group, so the identity embedding is itself Cartan. A closed subgroup
containing all Cartans must therefore contain the whole group. The quotient
data supplied by the structural statement are not needed for this case.

`cartanGeneration_of_isogenyReduction` applies strong induction on the
dimension of the actual dual-number Lie kernel, using the existing
`smoothConnectedAffineGroup_lieDimension_induction`. For the current group
`A`, the reduction hypothesis supplies a smooth connected affine group `B`,
an isogeny `q : A → B`, and lifting of every closed torus in `B` to a closed
torus in `A` through a torus isogeny.

If `B` is nilpotent, the preceding lemma proves generation. Otherwise the
reduction supplies a noncentral geometrically semisimple Lie element.
`isGeneratedByCartanSubgroups_of_geometricSemisimpleElement` applies the
assumed centralizer spanning statement and the proved semisimple-centralizer
smoothness theorem. Its smaller groups are identity components of proper
semisimple centralizers. Their maximal tori remain maximal in `B` by
`preservesMaximalTori_identityComponent_elementCentralizer_of_semisimple`,
with the first three structural hypotheses supplied explicitly.

The induction hypothesis concerns groups smaller than `A`. The existing
`Lie.finrank_kernel_eq_of_isogeny` identifies the Lie dimensions of `A` and
`B`, so every smaller centralizer group in `B` satisfies that bound. This
dimension equality does not assert that the differential of `q` is an
isomorphism or surjection, and permits inseparable isogenies.

Finally, `isGeneratedByCartanSubgroups_of_isogeny` reflects generation of `B`
to generation of `A` using the supplied torus lifts. That theorem's smooth
generated-envelope argument handles the arbitrary closed competitors in the
published conclusion. `cartanGenerationIsogenyInductionStatement` packages
this proof at exactly the displayed conditional proposition.

## Provenance and scope

This module assembles existing actual-group induction, centralizer, finite-map
reflection, and isogeny-dimension interfaces. It asserts no new external
structural theorem. The remaining mathematical work is to prove and publish
the explicit structural inputs, then apply this theorem to obtain the
unconditional `CartanGenerationStatement`. In particular, an isogeny with
the stated alternative and torus lifting is an input rather than a
construction in this module.
