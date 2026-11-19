# A separable closure stays a separable closure over an intermediate field

Let `k ⊆ E ⊆ K` be fields forming a scalar tower (`IsScalarTower k E K`), and let `K` be a
separable closure of `k` (Mathlib's `IsSepClosure k K`: `K` is separably closed and
separable over `k`).

* `isSepClosure_of_isScalarTower k E K : IsSepClosure E K`. Then `K` is also a separable
  closure of `E`. `K` is still separably closed. `K` is separable over `E` because it is
  separable over `k` and separability passes to the top of a tower (Mathlib's
  `Algebra.isSeparable_tower_top_of_isSeparable`).
* `isSepClosure_intermediateField`: the instance for an intermediate field
  `E : IntermediateField k K`, with `E` acting on `K` through its inclusion. In particular
  `SeparableClosure k` is a separable closure of each of its intermediate fields. The
  module checks this with an `example`.

The fields may lie in different universes.

## Use

For an intermediate field `E` of a separable closure `K / k`, the Galois pinning data
over `k` with splitting field `K` base-changes to Galois pinning data over `E` with the
same `K` (`GaloisPinningData.baseChange`, module `Reductive/GaloisPinningBaseChange`).
This instance says that `K` is then a separable closure of `E` too, so results stated for
a separable closure of the ground field apply over `E`.

## Provenance

Internal. This is the standard fact that a separable closure of `k` is a separable closure
of every intermediate field. The proof uses only the two Mathlib facts named above.
