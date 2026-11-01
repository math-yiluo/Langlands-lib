# The partial Fourier value on the first-block fiber

Author: Worker 1037.

This is derived internal material for JPSS (1983), Section 4.9. It concerns the
first-block fibers of the integrand of (4.7.1). The published partial Fourier value
`TwoBlockLowerUnfolding.partialSection h ψ μ Φ g` is
`∫ ψ(w_0) Φ((w, η) g) dw` for the supplied additive Haar measure.

`partialSection_firstBlockEmbedding_mul` proves

`(diag(v, 1) g Φ)~[ζ, η] = |det v|⁻¹ ∫ ψ((x v⁻¹)_0) Φ((x, η) g) dx`,

where `|·|` is the normalized absolute value. The proof uses
`(w, η) diag(v, 1) = (w v, η)` and the published determinant change of variables
`rowMeasure_map_vecMul`. The scalar scaling of the supplied Haar measure comes from
`padicScalarHaarScaling`. The supplied measure is not renormalized.
