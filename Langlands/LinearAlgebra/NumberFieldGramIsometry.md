# The quadratic-form Hasse principle implies the Gram-matrix version

`Langlands.NumberFieldGramIsometryStatement.{u}` is a `Prop`-valued internal
matrix version of the classical quadratic-form theorem. For every number field
`F`, every natural number `n`, and two symmetric invertible `n × n` matrices
`B₁` and `B₂` over `F`, it says that congruence after coefficient extension
to every actual completion implies congruence over `F`. Congruence means
`Q B₂ Qᵀ = B₁` for an invertible matrix `Q` over the field in question.

`numberFieldGramIsometry_of_quadratic` proves this implication from
`Langlands.NumberFieldQuadraticIsometryStatement`. It retains that classical
theorem as an explicit premise and does not prove either arithmetic statement
unconditionally.

The supporting `polar_nondegenerate_of_symmetric_unit` works over any
characteristic-zero field and finite coordinate type. The quadratic form of
a symmetric matrix `B` has polar bilinear form twice the bilinear form with
matrix `B`. Its determinant is nonzero because `B` is invertible. Cancelling
`2` proves that the quadratic polar form is nondegenerate on both sides.

To apply the classical theorem, the proof takes the native quadratic forms
`B₁.toQuadraticForm'` and `B₂.toQuadraticForm'`. At a place `v`, a local
Gram congruence gives an isometry of their coefficientwise extended matrix
forms. Composing it with the two `gramBaseChangeIsometry` comparisons produces
an isometry of the tensor scalar extensions that occur in the classical
statement. The resulting global quadratic isometry gives a congruence of
`B₁` and `B₂` by `gramCongruent_of_equivalent`.

Provenance is internal: this is a conditional formal consequence of the
separately stated classical quadratic isometry theorem and the compiled
Gram/quadratic comparison. It uses all finite and archimedean places, no
supplied local models, no restriction on dimension and no group-cohomology
Hasse-principle assumption.
