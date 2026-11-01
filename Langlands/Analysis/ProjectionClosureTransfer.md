# Finite-dimensional intersections and continuous projections

Author: Worker 94.

This internal topological linear-algebra lemma is derived directly from
Mathlib's closedness theorem for finite-dimensional subspaces.
It applies over any complete nontrivially normed field to a Hausdorff
topological vector space.

`Langlands.Analysis.inf_topologicalClosure_eq_of_projection` assumes
submodules `M` and `T` and an actual continuous linear map `P`. Its values
lie in `T`, it fixes every vector of `T`, it preserves `M`, and `M ⊓ T`
is finite-dimensional. The theorem concludes

`M.topologicalClosure ⊓ T = M ⊓ T`.

The implemented proof takes the inverse image under `P` of the
finite-dimensional, hence closed, subspace `M ⊓ T`. Preservation and the
range condition put `M` in this closed inverse image, so its closure also
lies there. On the intersection with `T`, the fixation condition
identifies `P x` with `x`. The reverse inclusion uses membership in the
closure.

The theorem constructs no projection and proves no dimension bound.
It uses no integration, local convexity, compact-group theory or density
assumption. Those obligations remain separate when it is applied to
compact types in the actual smooth representation.
