# Scheme-to-point Coxeter transport

Worker 1344. This is a conditional internal comparison, intended to supply
part of the structural indexing needed to apply the rational rank-one targets
when proving Corollary 1.10(b). It does not prove the corollary or the existence
of a scheme or point Coxeter realization.

`pointCoxeterSystem` transports a given scheme relative Weyl Coxeter system
through the published representative-preserving `weylEquiv`. The simple-root
labels remain the literal `SimpleRoot i ν`. Both exact normalizer and full
centralizer subgroup comparisons are explicit hypotheses.

The simple generators are their images under that equivalence. Length
preservation reuses `GroupScheme.coxeterLength_map_eq` with the identity
equivalence on labels; it introduces no second proof of that fact. Given
`IsRelativeWeylCoxeterRealization`, its right-descent clause and the published
`weylCharacterAction_weylEquiv` prove `RootLengthComparison` on actual points.

The standard-subgroup equality follows by mapping the closure of the same
simple generators. The realization's standard-subgroup clause and
`weylEquiv_map_schemeStandardWeyl` then identify this subgroup with the range
of the actual Levi Weyl inclusion, proving `actualLeviWeylIdentification`.
The proof does not replace the full centralizer denominator by the torus.

This content is derived from the named Library constructions and Mathlib's
Coxeter-system map and subgroup closure API. There is no new source claim,
representation-theoretic theorem, or use of classification, character
independence, a geometric lemma, adjointness, or cuspidal support.
`pointCoxeterSystem_positiveSimpleReflectionComparison` proves
`PositiveSimpleReflectionComparison` from the same scheme realization, with
splitness and finiteness of the scheme relative Weyl group explicit. It uses
the proved scheme `IsRelativeWeylCoxeterRealization.conj_simple_iff` in the
accompanying `SimpleReflectionConjugacy` module, then injectivity of `weylEquiv`
and its compatibility with the character action. The positivity condition is
retained. `pointCoxeterSystem_comparisons` groups the two root-sign comparisons
and the Levi Weyl identification for the same transported system. The scheme
reflection-label assertion is proved; existence of a scheme realization,
splitness, finiteness, and both point subgroup comparisons remain inputs.

The accompanying scheme proof includes a reflection conjugation and uniqueness
route suggested by Worker 181. Length preservation reuses Worker 913's lemma.
