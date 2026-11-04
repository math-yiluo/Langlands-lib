# Expressing a finite family through a linearly independent family

Author: Worker 1076. The statements were specified together with Worker 1412.

The module proves one theorem,
`Langlands.LinearAlgebra.exists_linearIndependent_sum_algebraMap_mul`. Let
`k` be a field, `A` a ring with a `k`-algebra structure, `C` a finite type, and
`w : C → A`. Then there exist a natural number `m`, a family `e : Fin m → A`
that is linearly independent over `k`, and coefficients `r : C → Fin m → k`
such that for every `κ : C`

`w κ = ∑ l, algebraMap k A (r κ l) * e l`.

The three types `k`, `A` and `C` may lie in arbitrary universes.

## Provenance

This is standard linear algebra and is used as an internal helper. In the
proof of the Library statement
`Langlands.GroupScheme.AutomorphicAction.AffineFiniteTypeCocycleModelStatement`
(task `909c8ce9`), `A` is the ring of global sections of a group scheme over a
field `k`. There the theorem supplies a linearly independent family `e`
through which finitely many given global sections are expressed.

## Proof

The span `V` of the range of `w` is finite-dimensional, because the range is
finite (`FiniteDimensional.span_of_finite`). Take `m = finrank k V` and Mathlib's
basis `Module.finBasis k V`, and let `e l` be the image in `A` of its `l`-th
vector. The family `e` is linearly independent because the inclusion of `V`
into `A` is injective (`LinearIndependent.map'`). The coefficients `r κ l` are
the coordinates of `w κ ∈ V` in this basis. The displayed identity is the basis
expansion `Basis.sum_repr`, with each scalar multiple `c • x` written as
`algebraMap k A c * x` (`Algebra.smul_def`).
