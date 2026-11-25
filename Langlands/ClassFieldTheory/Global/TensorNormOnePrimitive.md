# Norm-one torsion primitives on finite Galois refinements

Let `B/F` be finite and let `L/F` be a finite Galois coefficient extension.
The coefficients are the units of the actual tensor algebra `B ⊗[F] L`.
`TensorNormOnePrimitiveAfterRefinement` asks for a primitive of a given
crossed degree-two cochain after a finite Galois refinement. Every value
of the primitive must have determinant norm one and `n`-th power one.

If a tensor-unit cochain has norm-one differential, its norm is a scalar
crossed cocycle. When the cochain values have `n`-th power one, Hilbert 90
and fixed-field descent give a unit `s` of `F` and a radical `z` of `L`
whose Kummer cocycle is its norm. Assume that `B/F` is separable with a
compatible embedding in `L`, the characteristic is zero, and `n > 0`.
If `s = N(b) q^n` for units `b` of `B` and `q` of `F`, choose a tensor
`n`-th root of `b ⊗ 1` over a finite Galois refinement. Its norm and the
extended `z/q` have the same `n`-th power. The ratio is a root of unity.
Lift that ratio to a tensor root of unity and multiply the tensor radical
by the lift. This gives an adjusted tensor radical with the same `n`-th
power and norm exactly `z/q` after extension.

Dividing the extended cochain by the coboundary of this adjusted radical
makes every value have norm one. Its `n`-th power remains one because the
power of the radical comes from the fixed left factor. The degree-two
differential remains the specified extension of the original differential.
If `[B:F]` is coprime to `n`, the required norm factorization holds for
every `s`, so no norm factorization premise is needed in that case.
This is an internal cochain calculation for the adjoint norm-kernel case.
