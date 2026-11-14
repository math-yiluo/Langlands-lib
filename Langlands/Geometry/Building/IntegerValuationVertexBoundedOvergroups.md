# Bounded overgroups of vertex one-stabilizers

This internal prerequisite proves the overgroup-containment half of vertex
maximal boundedness for the original integer-valued building. It applies over
any field `k` with a valuative relation, a compatible valuation
`v : Valuation k (WithZero (Multiplicative ℤ))`, and supplied
`B : IntegerValuationBuildingData v G`. It assumes that the original quotient
has common translated apartments.

`IntegerValuation.VertexBoundedOvergroupStatement` says that, for every actual
vertex `y` and algebraically bounded subgroup `H` of the original
`rationalPoints G`, the inclusion `B.oneStabilizer y ≤ H` implies
`H ≤ B.oneStabilizer y`. The theorem `IntegerValuation.vertexBoundedOvergroup`
proves this proposition at arbitrary universe `u`.

The separate lemma
`IntegerValuationBuildingData.maximal_oneStabilizer_vertex_of_isAlgebraicallyBounded`
combines this conclusion with explicitly supplied algebraic boundedness of the
one-stabilizer. Boundedness of the one-stabilizer is not asserted by the
overgroup-containment proposition. The unconditional maximal-unramified target
therefore remains a separate closing obligation.

## Implemented proof

The proof first works in the original affine apartment.

1. For a bounded subgroup `H`, the normalizer elements belonging to `H` have a
   finite orbit at any apartment point, by the published theorem
   `finite_normalizer_orbit_of_isAlgebraicallyBounded`. The orbit contains the
   initial point and is invariant under that normalizer subgroup. Its finite
   affine centroid is consequently fixed by every normalizer element in `H`.
   This proves `exists_normalizer_fixed_of_isAlgebraicallyBounded`.

2. Suppose that `H` contains the one-stabilizer of an apartment vertex `x`.
   Every affine-root reflection whose hyperplane contains `x` lifts to an
   actual normalizer element in the sharp fixer of `{x}`, by
   `exists_sharpFixer_normalizer_eq_affineReflection`. The sharp fixer lies in
   the one-stabilizer, so every such reflection fixes the centroid. Evaluating
   the reflected root shows that the centroid lies on every root hyperplane
   through `x`.

3. The auxiliary torsor lemma
   `AffineRootSystem.eq_of_isVertex_of_vanishingRoots_torsor` shows that these
   hyperplanes determine `x` uniquely. Local finiteness supplies a positive
   displacement parameter for which every root nonzero at `x` retains its
   sign. The roots vanishing at `x` vanish along the displacement toward the
   proposed second point. Thus a point on this small segment belongs to the
   facet of `x`. That facet is the singleton `{x}`; cancelling the nonzero
   parameter gives equality. This is the torsor version of the published
   vector-space argument `eq_of_isVertex_of_vanishingRoots`. Together these
   steps prove `normalizer_fixes_vertex_of_isAlgebraicallyBounded`.

4. Common apartments give a factorization `g = p * n * q` for each `g ∈ H`,
   where `p` and `q` belong to the sharp fixer of `{x}` and `n` is in the
   actual normalizer. Both sharp-fixer factors belong to `H`, hence so does
   `n`. The preceding step makes `n` fix `x`, and all three factors fix its
   image in the original quotient. The published integer-valued
   character-kernel theorem places every element of the bounded subgroup
   `H` in `characterValuationKernel v G`. Fixing the vertex and belonging to
   that kernel is exactly membership in its one-stabilizer. This proves
   `le_oneStabilizer_apartment_vertex_of_isAlgebraicallyBounded`.

5. Write an arbitrary vertex as `g • B.apartmentMap x`. Pull back `H` by
   conjugation by `g`. This subgroup is bounded because it is contained in
   `{g⁻¹} * H * {g}`; the required finite-type instance comes from the
   connected-reductive building data. Conjugation carries the one-stabilizer
   of `x` into the original one-stabilizer. Applying the apartment result
   and conjugating back proves
   `le_oneStabilizer_vertex_of_isAlgebraicallyBounded`.

The argument uses the existing actual root reflections, finite normalizer
orbits, affine centroids and quotient factorization. This is an internal
derivation from those Library results; it makes no claim to implement a
literature proof through a metric fixed-point theorem. The field, group,
valuation, apartment torsor and quotient building are preserved throughout.
