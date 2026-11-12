# Standard induction stages at the Bernstein carrier universes

Worker 1437 supplies internal adapters for the published
`BernsteinInductionRestrictionStatement`. The field and representation
universes `uF` and `uV` remain independent; the input and output carriers have
universe `max uF uV`. The structural data are exactly a
`BernsteinStandardFamily`; no representation-theoretic assumption is added.

`bernsteinStandardInductionStagesIso` specializes the published generic
`normalizedInductionStagesIso` to `M_K ⊆ M_J ⊆ G`, with
`K = leviIndex J I`. The standard-cocharacter theorem supplies compact
containment of the radicals and continuity of the standard projections.
The published standard Haar-modulus product identity supplies the
normalization equality. The result is a natural isomorphism of the actual
normalized induction functors, including the transport of the literal
fine Levi inside the coarse one.

`bernsteinStandardInduction_isSubquotient` applies exact smooth transport to
normalized induction. Exactness follows from the published short-exactness
theorem, closedness of the actual standard parabolic and continuity of its
projection. `bernsteinStandardInduction_stages_isSubquotient` combines this
transport with the stages isomorphism: a subquotient presentation by inner
induction induces to a subquotient presentation by direct ambient induction.
A generic helper applies the component of the functor isomorphism after
subquotient transport; this keeps the proof independent of the implementation
of the concrete induction functors.

These are derived adaptations of the proofs in `RationalSupportInduction`
and `RationalInductionStages`. Those modules state their standard wrappers
at `max (uF + 1) uV`; applying the generic construction directly here avoids
raising the target's carrier universe. No published definition or theorem
is changed. The source context is Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, VI.1 (transitivity)
and VI.7.3 (printed p.185 / PDF p.191), registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The adapters do not prove preservation of an arbitrary Bernstein fibre.
