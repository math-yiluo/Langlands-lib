# Finite scheme-theoretic centres under arbitrary base change

Authors: Workers 1294, 1401 and 1490. The arbitrary-base
centre-representative argument adapts Worker 1401's centre base-change
proof. Worker 1490 contributed the interface and the separation of this
helper from the final semisimplicity theorem.

## Meaning

`FiniteCenter G` is data for a supplied representative of the entire
scheme-theoretic centre: an actual group scheme `C.group` over the base,
an inclusion `C.inclusion : C.group ⟶ G`, its
`IsSchemeTheoreticCenter` property, and finiteness of its structural
morphism. It packages the witnesses in `HasFiniteCenter G` without
choosing a representative from that proposition.

Let `b : S' ⟶ S` be any morphism of schemes in universe `u`. The construction
`FiniteCenter.baseChange` sends supplied finite centre data to its actual
pullback group and inclusion, with proofs that they remain a finite full
centre. The helper
`IsSchemeTheoreticCenter.baseChange` says that a given actual closed subgroup
representing the full all-test centre of `G` remains such a representative
after the actual pullback along `b`. The helper `HasFiniteCenter.baseChange`
says that a finite representative of that full centre stays finite after
the same pullback.

Both assertions retain the entire scheme-theoretic centre and its possibly
nonreduced structure. They need no reductivity assumption or restriction
to field-valued bases.

The construction is noncomputable because it uses the existing categorical
pullback functor. It makes no further choice of a centre representative.

## Implemented argument

For the first helper, preserve the closed immersion with
`IsClosedSubgroup.baseChange`. Rewrite its range using
`SubgroupFunctor.range_baseChangeHom`, the given range equality, and
`center_baseChange b G`.

For `FiniteCenter.baseChange`, use the pullback of the supplied group and
of its inclusion as the new data, and apply the first helper for its centre
property. Install the supplied finiteness as a local instance. The remaining
structural map is definitionally `Limits.pullback.snd C.group.X.hom b`,
which is finite by Mathlib's base-change instance for finite morphisms.

`FiniteCenter.hasFiniteCenter` forgets the supplied data to the existing
existential proposition. To prove `HasFiniteCenter.baseChange`, unpack
the actual representative supplied by `HasFiniteCenter G`, package it
as `FiniteCenter G`, apply the construction, and forget the resulting data.

## Provenance and scope

This data packaging and pullback construction are internal consequences of the Library predicates
`IsSchemeTheoreticCenter` and `HasFiniteCenter`, the full all-test centre
base-change identity, and Mathlib's finite-morphism pullback instance.
`FiniteCenter` adds a data interface for the existing existential witnesses;
it changes no existing mathematical predicate and asserts no centre existence
theorem. No new external source assertion is introduced.
The implementation imports the published
`Langlands.GroupScheme.Reductive.CenterBaseChangeProof`, adapts Worker
1401's centre-representative argument to an arbitrary base map, and packages
Worker 1294's finite-centre witness transport using the interface agreed
with Worker 1490.

This unit supplies the finite-centre part of semisimplicity ascent.
Connected-reductivity ascent and semisimplicity reflection remain separate
proof obligations.
