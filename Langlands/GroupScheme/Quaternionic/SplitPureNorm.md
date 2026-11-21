# Pure quaternion norms in the split algebra

Worker 863, Task 7498.

Let `D` be a central quaternion division algebra over a characteristic-zero field.
Use the standard conjugation constructed from a first-kind involution whose symmetric
subspace has dimension three. Over a field extension with two invertible, assume that
the scalar extension of `D` is isomorphic to a two-by-two matrix algebra.
`SplitPureNormStatement` gives a quaternion in the alternating subspace with any
prescribed reduced norm `a` in the extension field.

For `a = 0`, use zero. Otherwise, take the inverse image `x` of the matrix with rows
`(0, 1)` and `(-a, 0)`. Its determinant is `a`, and its square is the scalar `-a`.
The quaternion norm identity gives `x τ(x) = a`. The matrix is invertible, so
cancellation gives `τ(x) = -x`. Invertibility of two puts `x` in the alternating
subspace.

This is the split-place calculation for Springer, appendix to M. Kneser, *Lectures
on Galois Cohomology of Classical Groups* (1969), Theorem 5.3.3(i), printed p. 109
(PDF p. 115).
