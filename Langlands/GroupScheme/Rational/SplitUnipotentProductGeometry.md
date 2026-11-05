# Full-dimensional closed affine orbits

This is an internal geometric construction supporting the finite-field
split-unipotent product criterion. It is derived from the imported dimension,
closed-immersion, and actual homogeneous-quotient results, with no new source
assertion.

`surjective_of_closedImmersion_of_fullDimension` works over any field `k`.
Let `Y` be connected and quasi-compact, smooth of constant relative dimension
`d` over `k`, and let `i : X → Y` be a closed immersion. If the topological
Krull dimension of `X` is at least `d`, then `i` is surjective. Smoothness and
connectedness make `Y` irreducible, and its dimension is at most `d`. A proper
closed range would have dimension at least one less than `Y`. The closed
embedding identifies the dimension of `X` with that of its range, giving the
impossible inequality `d + 1 ≤ d`.

For the remaining declarations, `k` is algebraically closed. The actual group
schemes `G` and `U` are smooth, affine, and connected over `k`; `E` is affine.
The supplied `SchemeAction G U.X`, rational point `x`, closed subgroup map
`i : E → G`, and smoothness of `E` satisfy the exact fiber condition
`q(g) = q(h) ↔ g⁻¹h ∈ range(i)` on every relative scheme test, where `q` is
the original orbit map. Its topological range must be closed, and the supplied
Lie dimensions must satisfy `dim G = dim E + dim U`. No unipotence or finite
field hypothesis is asserted or used in these generic declarations.

`orbitImageInclusion_isIso_of_dimension` shows that the closed inclusion of
the actual schematic orbit image into `U` is an isomorphism. The imported
closed-orbit construction gives a smooth surjective homogeneous quotient whose
scheme and projection are this image and its canonical projection. Its
constant relative-dimension data give `dim G = dim E + quotientDimension`,
so the supplied equality identifies `quotientDimension` with `dim U`.
The quotient's rational identity section bounds its dimension from below.
The preceding closed-immersion result therefore makes its inclusion into `U`
surjective. Since the smooth target `U` is reduced, the surjective closed
immersion is an isomorphism.

`orbitImageIsoOfDimension` packages that same inclusion as a scheme
isomorphism; its forward morphism is the original orbit-image inclusion.
`orbitMap_smooth_surjective_of_dimension` factors the original orbit map as
the homogeneous-quotient projection followed by this inclusion, and concludes
that the actual orbit map is smooth and surjective.

The dimension equality and closedness hypotheses remain explicit here. The
finite-field product theorem must still derive them from its own unchanged
hypotheses, identify the two-sided subgroup-product orbit with the original
multiplication up to second-factor inversion, and descend the resulting
geometric properties to the finite field. This construction alone does not
prove that target theorem.
