# Finite terms for derived-series elements

Worker 1370.

This internal construction supports solvability transport for actual group schemes.
`DerivedTerm n` is finite syntax: an arbitrary input at level zero, the identity,
products and inverses at a fixed level, and commutators which raise the level by one.
Independent inputs are supplied to the two branches of a binary operation.

For a group scheme `G`, `domain G t` is an actual scheme over the base, built from
`G` and the base by finite relative products. `evaluation G t` is the actual scheme
morphism obtained from multiplication, inversion and the unit. Its values on every
test scheme belong to `derivedSeries n`. Conversely every element of that subgroup
is the value of one such finite term. The latter proof uses induction on the derived
series and subgroup closure, so products of arbitrarily many commutators remain
included. Smoothness of all domains follows by finite products from smoothness of G.

The syntax and its representing morphisms are an internal implementation, rather
than a definition asserted by the original literature. Its provenance is the
abstract derived-series criterion used in Milne, *Algebraic Groups* (2017),
Proposition 6.30, printed p.132 / PDF p.148, registered source
`milne-2017-algebraic-groups`. This module establishes no field-extension theorem.
