# The dual equal-rank gauge premise from a Whittaker–Schwartz estimate

This internal helper separates the second cusp factor and Fourier transform from the
analytic estimate needed for the dual half of `EqualUnfoldingGaugeStatement`.
Its provenance is derived from the published `CuspCentralBound`, `UnequalGaugeReduction`,
`UnfoldingDual`, and `SchwartzBruhatProof.Fourier` modules. It does not yet prove the
remaining Whittaker–Schwartz estimate or the unconditional gauge statement.

`DualEqualWhittakerSchwartzBound F T` says that a nonnegative threshold exists such that
for all standard characters, vectors of the realization `T`, Schwartz–Bruhat functions
`Φ`, and real exponents `σ` above that threshold, the lower integral

`∫ |W̃(g)| |Φ(e_n g)| |det g|^σ dg`

over `N_n(𝔸) \ GL_n(𝔸)` is finite. Here `n = r + 1`, `W̃` is the Library's dual
of `cuspWhittaker F T ψ v`, and the measure is `whittakerQuotientMeasure`.
The threshold may depend on `F`, `r`, and `T`, but is uniform in the other data.

The theorem `EqualGaugeDualReduction.dualEqualWhittakerGaugeIntegrable_of_schwartzBound`
proves that this bound implies `DualEqualWhittakerGaugeIntegrable F T T'` for every
second realization `T'`. The proof takes the fixed central exponent `β` of the dual
cusp functions of `T'` from `CuspCentralBound.exists_norm_dualCuspFunction_le`.
If the estimate has threshold `C₀`, the resulting gauge threshold is `max 0 (C₀ - β)`.
For each vector of `T'`, the dual cusp factor is bounded by `C' |det g|^β`, with
`C' ≥ 0` depending on that vector. For `Re s` above the gauge threshold, the shifted
exponent `σ = Re s + β` exceeds `C₀`.

Fourier stability from `SchwartzBruhatProof.fourierTransform_mem_and_inversion` allows
the estimate to be applied to `Φ̂`. The dual Whittaker function transforms under
`N_n(𝔸)` by the inverse generic character, which has absolute value one. The last row
and determinant norm are left unipotent invariant. Thus the product
`|W̃(g)| |Φ̂(e_n g)| |det g|^σ` is measurable and left unipotent invariant, and
`GaugeReduction.lintegral_rationalQuotient_eq` transfers its finite integral to
`N_n(F) \ GL_n(𝔸)`. Pointwise domination then proves integrability of the gauge
kernel. Rational left invariance and `LeftCosetSpace.lift` provide measurability on
this quotient. The preliminary lemma `norm_dualCuspWhittaker_unipotent_mul` records
the absolute-value invariance used here.

All field, number-field, compact-adelic-quotient, rank and universe assumptions are
retained. No actual contragredient realization or identification of cusp embeddings
is assumed or constructed.
