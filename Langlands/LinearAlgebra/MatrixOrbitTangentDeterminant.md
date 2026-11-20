# Absolute determinants on real matrix orbit tangents

`matrixConjugationTangent A` sends a real square matrix `X` to `X * A - A * X`. On its range, `matrixOrbitTangentForm` pairs `t` with `s` by taking the trace of `t * J(s)`, where `J` is a right inverse to the commutator map on its range. The trace pairing of the range with the kernel vanishes. Every matrix is the sum of an element in the image of `J` and a kernel element, so nondegeneracy of the ambient trace form gives left nondegeneracy of the tangent form. Right nondegeneracy follows because a matrix orthogonal to the range lies in the kernel.

An ambient trace isometry that intertwines the commutator up to a scalar of absolute value one restricts to the tangent and multiplies its form by that scalar. A nondegenerate form identifies the tangent with its dual, so the square of the restricted determinant is the determinant of scalar multiplication. Taking absolute values gives one. Conjugation by a unit commuting with `A` has scalar `1`. Transpose followed by a conjugation bringing `Aᵀ` back to `A` has scalar `-1` because transpose reverses multiplication.

These internal lemmas supply the orbit tangent Jacobians for local distribution comparison in the real transpose argument.
