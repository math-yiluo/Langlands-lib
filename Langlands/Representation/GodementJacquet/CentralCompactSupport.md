# Compact matrix support on central saturations

This internal topological helper concerns the actual group of invertible
matrices over a Hausdorff topological field. `scalarSaturation K` is the set
of scalar multiples of elements of `K`, with nonzero scalars represented by
field units.

For compact `K` in GL and a compact set `S` of matrices excluding zero,
`exists_isCompact_cover_scalarSaturation` constructs a compact set in GL
containing every element of the saturation whose underlying matrix lies in
`S`. The proof uses the compact product `S × K`. On the closed locus where
`x` is a scalar multiple of `k`, the scalar is the `(0,0)` entry of
`x k⁻¹`. It cannot vanish because `S` excludes zero. Its continuous lift
to field units gives a continuous map from this compact locus to GL, and
the image is the required compact cover.

A locally constant matrix test that is zero at zero has closed support
excluding zero. The final theorem applies the compact cover to its compact
support and to the support of an arbitrary coefficient function contained
in a compact scalar saturation. It proves compact support of the product
on GL. The existence of such a coefficient cover remains an explicit
representation-theoretic obligation. These are derived internal lemmas,
with no appeal to an external existence assertion.
