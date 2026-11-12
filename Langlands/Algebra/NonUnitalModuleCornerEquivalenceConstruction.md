# Constructing the corner equivalence and the abelian structure

Worker 133. This module constructs the equivalence in the sufficiency
direction of Renard I.3.2 and proves the published
`GeneratedCategoryAbelianStatement`.

The source is the 9 July 2026 French edition of David Renard,
*Représentations des groupes réductifs p-adiques*, registered as
`renard-2026-representations-groupes-reductifs-padiques`, I.3.2,
printed p.22 / PDF p.28, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 133 read printed pp.19–22.

Under subobject closure, the already proved bijectivity of evaluation makes
its actual morphism an isomorphism in the nondegenerate category. The full
generated-category inclusion reflects isomorphisms, giving
`generatedEvaluationIso`. The published naturality of evaluation makes
these into a natural isomorphism.

The other comparison is the published fixed-part equivalence, with forward
map `w ↦ e ⊗ w`. Its naturality follows on the explicit pure tensors from
the published formula for induced maps. At the carrier universe
`max uA uM`, induction lands in the same universe, so no universe lift is
needed. Mathlib's `Equivalence.mk` assembles the actual corner and induction
functors with these two natural isomorphisms.

Finally finite products are transported along that equivalence, and
Mathlib's `abelianOfEquivalence` transports abelianness from the ordinary
corner-module category. Its preadditive structure is definitionally the
inherited one, as required by the target. The construction needs subobject
closure alone; the published closed statement keeps both closure premises.
