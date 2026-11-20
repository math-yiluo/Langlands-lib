# Real standard membership from compact block slices

Let \(d_i\) be ordered lists of real blocks, and let \(f\) belong to the
principal series of the position characters of their concatenation.
Suppose that for every block \(i\) and every ambient point \(g\), the scalar
function \(k\mapsto f(\iota_i(k)g)\) on the block orthogonal group is
the restriction of some function in the real standard module of \(d_i\).
Then \(f\) belongs to the real standard module of the concatenated list.

The proof locates each two-dimensional induction block of the concatenation
in its unique ordered block list by `finSigmaFinEquiv`. The position
formula identifies its rotation with the image of the local rotation
under the block embedding. Every such rotation is orthogonal. The
hypothesis on the compact slice therefore identifies the required ambient
Fourier coefficient at \(g\) with the corresponding block Fourier
coefficient at the identity. The latter vanishes by membership in the
block's real standard module. The proof combines these Fourier conditions
with the supplied principal-series membership.

The result is an internal consequence of the defining conditions of
[`StandardModule`](StandardModule.md). It uses the block position formula
in [`RealLeviSlices`](RealLeviSlices.md) and the rotation comparison in
[`RealLeviProducts`](RealLeviProducts.md). It supplies the real
Fourier-vanishing part of the local induction-in-stages comparison.
