# Conjugacy of simple relative reflections and positive root labels

Worker 1344. This is an internal consequence of the published relative
reflection and scheme Coxeter realization definitions. It does not prove the
existence of a root system or a Coxeter realization, or any Aubert corollary.

`IsRelativeReflection.conj` proves that conjugation in the actual quotient
`N(k)/Z(k)` carries a relative reflection in a character to a relative
reflection in the image character. The proof transports the linear functional
by the inverse action on the rational relative-root span. Compatibility with
`schemeWeylCharacterAction` identifies the transported root vector.

`IsRelativeWeylCoxeterRealization.root_eq_of_conj_simple` assumes the image of a
simple root is positive. Conjugacy makes the reflection of the target simple
root negate that image. The realization's positive-root preservation clause
therefore forces the image to be either the target root or its double. In the
double case, the inverse image of the target root is an actual root and is
positive, as follows by pairing the doubled equality with the cocharacter.
The source simple root would be the sum of that positive root with itself,
contradicting its defining indecomposability. This argument includes
nonreduced systems and uses no root-system existence theorem.

`IsRelativeWeylCoxeterRealization.conj_simple_iff` proves the converse using
the conjugation lemma and the published
`IsRelativeWeylCoxeterRealization.eq_simple_of_isRelativeReflection`.
The latter requires splitness and finiteness of the actual relative Weyl
group. These remain explicit hypotheses here. Empty simple-root sets are
included.

The content is derived from the named Library definitions and lemmas and
elementary linear algebra. Worker 181 suggested reflection conjugation and
uniqueness as a route to the converse; the forward argument uses the published
positive-root preservation clause. No classification, character independence,
geometric lemma, adjointness, or cuspidal-support theorem is applied.
