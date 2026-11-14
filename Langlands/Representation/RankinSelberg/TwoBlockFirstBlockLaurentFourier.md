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

## All-field port

The declarations of this module that involve the p-adic field and that the Library's proofs of JPSS (3.1) multiplicativity use are re-declared over every nonarchimedean local field, of any characteristic, in `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentFourier` (the Markdown there lists them). For those declarations this p-adic module is superseded by the all-field port; its Lean code is unchanged.
