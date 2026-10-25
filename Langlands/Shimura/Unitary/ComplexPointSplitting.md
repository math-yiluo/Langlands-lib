# Splitting actual complex points of the rational Harris group

Let `D` be the central-simple unitary datum over the totally real number field
`E` and its totally complex quadratic extension `K`, with the scalar towers in
the Lean variables. Let `C` be actual Harris signature charts at a choice `Φ` of
complex embeddings over the real places. The coordinate comparison theorems also
retain `hΦ : IsCMSection E K Φ`.

`complexRationalPointSplitting` is a multiplicative equivalence from the actual
points of `D.rationalGroupScheme` on `Spec ℂ`, regarded over `Spec ℚ`, to a family
of invertible `n` by `n` complex matrices indexed by `E →+* ℝ`, together with one
complex scalar unit. It composes `rationalAffinePointsEquiv` with the published
`scalarGroupSplitting`. Neither its construction nor the scalar-coordinate
identity needs the CM-section compatibility hypothesis.

`complexRationalPointSplitting_multiplier` identifies the scalar coordinate with
`complexPointMultiplier`. Given `hΦ`, `complexRationalPointSplitting_matrix`
identifies the selected matrix at each real place `τ` with
`complexEmbeddingPointMatrices C hΦ x (Φ τ)`. The proof uses the embedding-factor
formula and equality of the iterated complex and scalar matrix decompositions.
Consequently `complexRationalPoint_ext` shows that these selected matrices and
the common multiplier determine the entire actual point: apply injectivity of
the multiplicative equivalence, then equality of both product coordinates.

`complexMatrixPoint` applies the inverse equivalence to an arbitrary family of
matrix units and multiplier one. `complexMatrixPoint_matrices` and
`complexMatrixPoint_multiplier` prove that all prescribed matrices are realized
simultaneously and that the multiplier is one. Both follow from the inverse law
of the equivalence and the coordinate comparisons.

This is an internal construction from the published rational affine-point and
scalar-splitting equivalences. It assumes no matrix-innerness theorem and adds
no literature claim. It supplies points that can be used as simultaneous
conjugators; it does not yet prove Galois cocharacter conjugacy, a reflex-field
comparison, or equality of scheme morphisms from equality on complex points.
