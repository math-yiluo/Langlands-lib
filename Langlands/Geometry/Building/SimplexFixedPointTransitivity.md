# A unique fixed point in a finite simplex forces vertex transitivity

Author: Worker 227.

This is an internal affine-geometric support result for the building argument
in Task 6205. It proves the finite-simplex implication used in the discussion
of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, §9.2.4 (printed p. 327,
PDF p. 358), and in the proof of Theorem 10.3.1. The implemented proof uses
orbit centroids and uniqueness of affine coordinates.

`SimplexFixedPointSubsingleton p ρ` says that the common fixed points of
`ρ γ` in `convexHull ℝ (Set.range p)` form a subsingleton. Here `I` is a finite
set with a group action, `V` is a real vector space, `p : I → V`, and each
`ρ γ` is an affine self-map of `V`. No topology or norm on `V` is assumed.

`exists_smul_eq_of_simplexFixedPointSubsingleton` assumes additionally that
`p` is affinely independent and that `ρ γ (p i) = p (γ • i)`. It proves
`∀ i j, ∃ γ, γ • i = j`. The group may be infinite. The maps are only required
to extend the given group action on the vertices; group laws on all of `V`
are unnecessary for this conclusion. In particular, the result applies to
an affine action on `V` with an equivariant vertex family.

For each vertex, its orbit is a nonempty finite subset of `I`. Each group
element permutes this subset. Affine maps preserve affine combinations,
so its centroid is fixed by every `ρ γ`; nonnegative weights of total one
place it in the convex hull. The subsingleton hypothesis equates the
centroids of any two orbits. Affine independence then equates their
indicator weight functions. The weight at the second vertex is the
reciprocal of its nonzero orbit cardinality, so it is nonzero. That vertex
must therefore belong to the first orbit.

The result supplies only this finite affine-geometric step. It does not
construct a chamber or a building, identify a Galois-fixed building, prove
unramified splitting, or compare a relative Cartan matrix with an absolute
one. In particular it does not prove
`Langlands.GroupScheme.LocalAnisotropicAffineDiagramStatement`.
