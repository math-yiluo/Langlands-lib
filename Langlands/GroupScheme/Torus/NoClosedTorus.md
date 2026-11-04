# Absence of nontrivial closed tori

Author: Worker 1487.

`Langlands.GroupScheme.HasNoNontrivialClosedTorus` is an internal
predicate for a group scheme over any field `k : Type u`. It says that
every closed inclusion of a torus defined over `k` has trivial range on
every relative test scheme. Tori need not be split. No smoothness,
affineness or connectedness hypothesis is part of this predicate.

This is a derived interface for the induction used in the proof of
`NoTorusUnipotentStatement`. That published target assumes triviality
of every homomorphism from a torus. The lemma `of_forall_hom` implies
the present predicate by specializing to closed inclusions. No converse
is asserted here.

The elementary lemmas in the predicate's namespace are proved as follows.

- `of_closedSubgroup` composes closed immersions. Triviality of the
  composite range reflects along the monomorphism of the ambient
  inclusion by `SubgroupFunctor.range_comp_eq_bot_iff`.
- `of_torus_lifting` assumes that every closed target torus is the image
  of a closed source torus under an actual isogeny of tori, with a
  commuting square. The source inclusion is zero because its all-test
  range is bottom. Flat surjectivity makes the torus isogeny an
  epimorphism of schemes, then of objects over the base, then of group
  objects. Cancellation shows that the target inclusion is zero and
  hence has bottom range. Finiteness is available in `IsIsogeny` but
  is not needed for this cancellation. No isogeny assumption on the
  ambient map is required.
- `isUnipotent_of_nilpotent` assumes the unproved proposition
  `NilpotentCentralTorusStatement`. Its exhibited maximal torus is a
  closed torus, so its range is bottom. The actual fppf quotient by
  that range is therefore isomorphic to the original group, and
  unipotence transfers across this isomorphism.
- `isUnipotent_of_finiteField` assumes both unproved propositions
  `FiniteFieldGeometricMaximalTorusStatement` and
  `AlgClosedTrivialMaximalTorusUnipotentStatement`. The former supplies
  a closed torus whose algebraic-closure base change is maximal.
  Its range is bottom, and remains bottom after the actual base
  change. The latter proposition makes the base-changed group
  unipotent. Smooth connected affine groups remain connected under
  this field extension; smoothness and affineness also base change.
  The field-reflection proof then yields unipotence over `k`.

The provenance is internal: these are elementary adapters for the
existing all-test range, closed-subgroup, isogeny, quotient and
field-reflection APIs. The two conditional unipotence proofs implement
the same reductions as `NoTorusBasicReductionProof`, with the weaker
closed-inclusion premise. The mathematical provenance of the structural
input propositions is recorded in their own paired Markdown files.
Their truth is not asserted by this module.

Only the standalone elementary lemma
`SubgroupFunctor.eq_zero_of_range_eq_bot` is used from
`NoTorusBaseChangeReduction`. The conditional theorem in that module
which consumes `NoTorusUnipotentStatement` is not applied. This module
neither assumes nor proves the arbitrary-field no-torus theorem,
preservation of absence of closed tori under arbitrary field extensions,
or reflection of unipotence under isogenies.
