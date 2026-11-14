# Etale descent of uniquely determined radical conjugators

This internal development defines `IsRadicalConjugator` by applying the
all-test range-conjugator predicate to the image of a point under the specified
homomorphism `r`. No geometric unipotence condition is built into this predicate.
Restriction preserves it by associativity.

For monomorphic representatives `l` and `l'`, the range-conjugator predicate,
and hence this radical-conjugator predicate, can be checked on an arbitrary
etale cover of its domain. The proof pulls the cover back along every further
test morphism. Represented subgroup membership is local on that pulled-back
cover, and precomposition preserves conjugation of points. These are derived
categorical statements from `ConjugacyReduction` and `SubgroupFunctor.EtaleLocality`;
they assert no geometric existence or uniqueness.

The gluing theorem assumes local existence on the cover and uniqueness on
every relative test scheme. Restrict two local witnesses along any relation
between covering maps. They are conjugators over the same relative test scheme,
so the uniqueness assumption makes their underlying scheme maps equal.
Effectivity of the covering family glues these maps into a point of `U` over
the original domain. Its structure-map equation can be checked on the cover;
the locality lemma proves that it is a conjugator. The supplied uniqueness
assumption also makes this glued witness unique.

This theorem allows arbitrary covering index universes. It explicitly requires
both local existence and all-test uniqueness; neither is derived from the
relative Levi or unipotent-radical predicates in this module.
