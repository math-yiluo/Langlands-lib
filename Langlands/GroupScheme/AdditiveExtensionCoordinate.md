# Additive coordinates on affine extensions

Worker 1330.

This internal construction supports the proof of
`LinearAdditiveExtensionSplittingStatement`. For a flat surjective homomorphism
`q : E → H` of affine group schemes over an affine base, any actual
homomorphism from its full scheme kernel to a finite dimensional vector group
extends to a regular map `f` on `E` such that
`f(g) - f(h) = a(g h⁻¹)` whenever `q(g) = q(h)`.
The right side reads the difference through the actual kernel.
The equality holds on every test scheme. No smoothness, reducedness or
scheme section of `q` is required, and `a` need not be an embedding.

The proof first constructs the actual kernel difference and verifies its
naturality and cocycle identity. Each vector coordinate gives an additive
cocycle on the affine faithfully flat cover `E → H`. The Library theorem
`AffineAdditiveCocycle.AddCocycle.exists_coboundary`, which implements degree one
exactness of the faithfully flat Amitsur complex, supplies a regular scalar
primitive for each coordinate. The vector point with these primitives as
coordinates is the required regular map. Its fibre identity follows by
pulling the cocycle formula back along arbitrary test scheme points.

This is a derived construction using the existing actual kernel, vector group
and Amitsur exactness APIs. It does not yet produce a homomorphic section or
assert the splitting theorem. It implements the additive torsor part of the
extension argument used in Milne, *Algebraic Groups*, corrected 2022 reprint,
Section 15h; the later proper-kernel reduction in Theorem 15.34(d) remains
separate.
