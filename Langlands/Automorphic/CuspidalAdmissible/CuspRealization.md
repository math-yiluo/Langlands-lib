# The cusp estimate for a cuspidal realization

Module: `Langlands.Automorphic.CuspidalAdmissible.CuspRealization`. Provenance: internal; a
square-integral form of the classical decay of cusp forms on Siegel sets, in the form needed
for the joint admissibility proof.

## Matrix facts (namespace `Langlands.Global`)

- `isUnitriangular_blockUnipotent`: block unipotent matrices `[[1, X], [0, 1]]` (reindexed
  along `Fin a ⊕ Fin b ≃ Fin n`) are upper unitriangular.
- `ofInfinite_apply`, `isUnitriangular_ofInfinite`: the entries of `ofInfinite g` are
  `(g_ij, δ_ij)`; unitriangularity passes to `ofInfinite`.
- `determinantNorm_of_isUnitriangular`: unitriangular adelic matrices have determinant norm `1`.

## Cusp regions (namespace `Langlands.Automorphic.CuspidalAdmissible`)

- `cuspRegion ΩN C c Q₁ K a T`: points `g` of the Siegel set `siegelSetGL ΩN C c` lying over
  the band, written `g = torInf(x) · q` with `q ∈ Q₁`, `x` in the chamber with constant `K`,
  and `chamberDrop x a > T`.
- `bandNorm S f = ∫_band |f|² d(quotientHaarMeasure)`; `basisDerivative S k f` is the action of
  the enveloping generator of `lieDirection k` (the `k`-th fixed basis direction).
- `slice_data_one`: the archimedean slices of a realized vector are smooth with
  `lieDirection k` derivatives the slices of `basisDerivative S k f` (Library `slice_data`).
- `cuspRegion_gap`: on `cuspRegion … a T`, every across-the-block gap `x_r - x_p`
  (`p` before `a`, `r` from `a` on) is at most `-(T - 2nK)` (`gap_le_of_chamber`).
- `point_mul_mem_band`: left translation by a unitriangular element keeps the band.
- `siegelMultiplicity ΩN C c = #{γ : γ 𝔖 ∩ 𝔖 ≠ ∅}` (as an extended real) and
  `siegelMultiplicity_ne_top hSF …`: it is finite, given Siegel finiteness `hSF`
  (`SiegelSetGLFinitenessStatement`).
- `lintegral_siegelBand_le`: `∫_{𝔖 ∩ band} |f|² d(matrixHaarMeasure) ≤
  siegelMultiplicity · bandNorm f` (`lintegral_le_mul_quotient` with
  `#{γ : γ x ∈ 𝔖} ≤ #{γ : γ 𝔖 ∩ 𝔖 ≠ ∅}`, `encard_rational_mul_mem_le`).

## Main estimate

`exists_cuspRegion_le S hSF hS L hL hΩ hΩN hC hC1 hc hQ₁ hK a ha`: for a cuspidal realization,
an open subgroup `L`, a Siegel set with compact data, compact `Q₁`, `K ≥ 0` and a block
position `a > 0`, there is a finite `c₁` such that for every `T ≥ 2nK` and every
`L`-invariant vector `e`,

`∫_{cuspRegion … a T} |e|² d(matrixHaarMeasure) ≤ exp(-(T - 2nK))² · c₁ · ∑_k bandNorm(D_k e)`.

Proof: apply `exists_lintegral_cusp_le` (module `CuspIntegral`) to the block `a + (n - a) = n`
with the vanishing constant term of `S` (`constantTerm_eq_zero`), `ℓ = T - 2nK`, `R` the cusp
region (gaps by `cuspRegion_gap`) and `t = 𝔖' ∩ band`, where `𝔖'` is the Siegel set with
unipotent data `U · ΩN`, `U` the compact set of archimedean block unipotents `u(V)`, `V ∈ 𝒲`
(`isCompact_mul_image`, `isUnitriangular_mul_image`, `mul_mem_siegelSetGL`,
`point_mul_mem_band`). Then `lintegral_siegelBand_le` for `𝔖'` bounds each derivative
integral by `siegelMultiplicity(𝔖') · bandNorm(D_k e)`; `c₁ = B² · siegelMultiplicity(𝔖')`.
