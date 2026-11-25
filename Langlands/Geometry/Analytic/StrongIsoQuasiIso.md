# Actual strong isomorphisms are full quasi-isomorphisms

This internal module proves that inverse strong morphisms in the
actual saturated category satisfy the full affinoid-test
quasi-isomorphism property. The field, ambient-space and atlas-index
universes `u, v, w` remain independent. `K` is a complete ultrametric
normed field; no separation assumption on either space is made.

`isQuasiIso_of_inverse` takes actual inverse strong maps `f, g` and their
two entire composition equations. Their continuous maps give a
homeomorphism. For an admissible source chart `i` and target chart `j` of
`f`, choose a target chart `k` for `g` on `j`, and a target chart `l` for
`f` on `k`. The inverse equations imply containments of chart `i` in `k`
and chart `j` in `l`. The saturated-composition equations identify the
bounded composites with the original full domain restrictions `i → k`
and `j → l`.

The latter restriction represents a domain against every affinoid test,
so the intermediate bounded map for `g` cancels maps to any such test:
precompose the proposed equality with the remaining bounded factor and
apply full-domain uniqueness. Given a bounded test map on chart `j` whose
spectrum image is in `f`'s chart image, compose with that intermediate
map. The inverse ambient equation places its image in chart `i` inside
`k`. The full domain restriction `i → k` factors it uniquely. Cancellation
of the intermediate map proves the required equation over chart `j`;
uniqueness follows from the first domain restriction. This gives the full
factorization property of `f`'s actual bounded pullback. Its closed image
and exact range are the existing `isClosed_chartImageLocus` and
`range_pullback` results.

`isQuasiIso_of_isIso` applies this argument to the actual inverse stored
by an isomorphism. The proof compares complete bounded maps and tests all
presented affinoid algebras; it does not reconstruct maps from their
spectrum-point values. All input facts are internal published category,
atlas and domain constructions, with no new literature translation.
