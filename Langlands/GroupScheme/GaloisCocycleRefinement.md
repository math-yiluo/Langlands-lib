# Finite Galois refinement of actual scheme cocycles

This derived module uses the existing all-test scheme cocycle, its finite-Galois
value detection, and the actual coefficient-point tower and fixed-point descent
constructions. It applies to affine group schemes, including noncommutative
ones, over a field in arbitrary universe `u`.

The imported `Cocycle.refine ξ p` from
[`CocycleRefinement`](CocycleRefinement.md) restricts the natural family of cocycle values along a map
`p : V → U` of covers. Its value at `a,b : Z → V` is the original value at
`a ≫ p,b ≫ p`. Naturality and the cocycle identity are inherited from the
original family. The same module's `Cocycle.toFun_self` proves that diagonal values are the
identity by cancellation in the actual point group.

For a tower `k ⊆ L ⊆ M`, `GaloisCocycle.coverMap` is the actual spectrum map
from the larger coefficient field to the intermediate field. If `L/k` is
normal, restriction of automorphisms commutes with this map, as expressed by
`arrow_coverMap`. This follows from the algebraic restriction formula and the
contravariance of the spectrum functor. Naturality then gives `value_refine`:
the refined value at an automorphism of `M/k` is the extension of the original
value at its restriction to `L/k`.

`isTrivial_of_refine` assumes finite Galois extensions `L/k`, `M/k`, and `M/L`,
the compatible field tower, and affineness of the group scheme. A trivial refined
cocycle supplies one actual point over `M`. Its coboundary equation at every
relative automorphism of `M/L` has identity left side, because the restriction
is the identity and the original cocycle has identity diagonal values.
Consequently that point is fixed by every relative automorphism. The existing
`relativeDescend` constructs a point over `L` whose extension is the chosen
point. For each automorphism of `L/k`, lift it to `M/k`, apply the refined
coboundary equation, and use compatibility of conjugation with extension.
Injectivity of extension on affine coefficient points gives the coboundary
equation over `L`. The proved finite-Galois value criterion recovers the original
all-test `Cocycle.IsTrivial` over the original cover.

No cohomology-vanishing assumption enters this descent lemma. A source of
triviality over a larger cover is still needed in its applications.
