# Uniform integrable decay for the real alternate triangular columns

This module is the real counterpart of the Library's `ComplexGapAlternateColumnDecay`. `H` is the real
matrix height `realMatrixHeight`.

`unipotentDecay p Z = (1 + ‖upperEntryCoordinates (q + 1) Z^{-1}‖)^{-p}` is radial decay in the free
entries of the inverse of `Z ∈ N_{q+1}(ℝ)`.

* `norm_triangularFourier_le`: for `a : ℝˣ`, Schwartz column tests `Φ_j` (`j < q`) and `p : ℕ`, there is
  `C ≥ 0` with `‖triangularFourier k q a B Φ Z‖ ≤ C · H(B)^p · unipotentDecay p Z` for all
  `B ∈ GL_{k+q+1}(ℝ)` and `Z`. The Fourier arguments are the vectors
  `v_j = B^{-T} · transposeColumn k q Z^{-1} j`. Applying `B^T` to `v_j` recovers the padded transpose
  columns `transposeColumn k q Z^{-1} j` of `Z^{-1}`, and these contain every strict upper entry of
  `Z^{-1}`. The private estimate `norm_entryCoordinates_le` therefore bounds
  `1 + ‖upperEntryCoordinates (q + 1) Z^{-1}‖` by `(k + q + 1) H(B) ∏_j (1 + ‖v_j‖)`, since each
  entry of `B^T v_j` costs at most `(k + q + 1) H(B) ‖v_j‖`. The Fourier transforms are bounded by
  Schwartz seminorms of order `p` of the Schwartz functions
  `RealGapColumnFourier.columnSchwartzFourier a Φ_j`.
* `integrable_unipotentDecay`: for an additive Haar measure `μ` on `ℝ` and `p` larger than the real
  dimension of the entry space, `unipotentDecay p` is integrable for `entryHaar μ (q + 1)`; the entry
  coordinates carry `entryHaar` to a product Haar measure, `(1 + ‖x‖)^{-p}` is integrable there, and the
  entry Haar measure is inversion invariant (`measurePreserving_entryHaar_inv`).

`RealGapAlternateColumnDecayStatement` (proved by `realGapAlternateColumnDecay`): for all `k`, `q`,
`a : ℝˣ` and tests `Φ`, there are `p` and `C ≥ 0` such that `unipotentDecay p` is integrable for
`entryHaar (realSelfDualMeasure a) (q + 1)` and the bound of `norm_triangularFourier_le` holds.

This is an internal estimate supporting the absolute convergence of the larger-gap integrals in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.
