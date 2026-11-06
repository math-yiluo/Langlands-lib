# Uniqueness of geometric local Weil reciprocity

Author: Worker 584.

`Langlands.LocalClassField.GeometricWeilReciprocityUniqueness` is the
uniqueness-only fragment of the published
`WeilReciprocityExistenceUniqueness` proposition in
[WeilReciprocityStatement](WeilReciprocityStatement.md). It is an internal
decomposition of that existing target, with no new literature assertion.

The proposition quantifies every prime `p`, every `PadicField.{u} p` in
an unrestricted carrier universe, every `T : F.TopologicalData`, and
two actual continuous multiplicative equivalences from the topological
abelianization of the field's constructed local Weil group to its
multiplicative group. If both candidates satisfy the unchanged
`GeometricWeilReciprocityRelation F T`, they must be equal as continuous
multiplicative equivalences. That relation includes geometric order and
the induced geometric profinite reciprocity relation; neither hypothesis
is replaced by a weaker normalization condition.

The only implemented proof in this module is
`geometricWeilReciprocityUniqueness_of_existenceUniqueness`. It eliminates
the existing `∃!` conclusion at the supplied field and topology, applies
its uniqueness clause to each of the two candidates, and composes the
resulting equalities. It assumes the existing existence-and-uniqueness
proposition and does not prove either that proposition or the new
uniqueness proposition unconditionally.

This fragment lets a consumer that already has two normalized candidates
request their equality without also requesting construction of a third
one. In particular, the epsilon-inheritance target compares its supplied
geometric candidate with the one witnessed by the supercuspidal
correspondence. A proof of the fragment is still required; this statement
does not add a uniqueness assumption to that target or prove epsilon
inheritance.
