# Relative unit norms inside a prescribed finite extension

Author: Worker 1587.

This internal adapter applies the published local unit-norm theorem to an
intermediate field `E` of a fixed finite extension `L` of the maximal
unramified extension of a nonarchimedean local field `F`. Bounded units of
`E`, measured by their images in `L`, have bounded norm preimages in `L`.

The adapter lifts `E` into the fixed separable closure, views `L` as an
extension of this lifted field, and applies
`nestedIntermediate_unit_norm_surjective`. The lift equivalence preserves
the spectral valuations. Mathlib's invariance of the algebra norm under a
base ring equivalence identifies the resulting norm with `Algebra.norm E`
on the original extension `L/E`. A choice function records a preimage and
its two proved properties.

No Galois assumption on `L/E` is needed. The universe, the characteristic,
and the actual spectral valuations agree with the published theorem.
