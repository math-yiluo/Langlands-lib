# Principal-series functions built from level factors

Fix level data `h b : ℕ → ℕ` (numbers of holomorphic and antiholomorphic determinant factors at
each level) and `dτ : ℕ → ℂ` (modulus increments).

## Definitions

- `LevelMatrices n h b`: for every level `m`, matrices `A m j` (`j < h m`) and `B m j`
  (`j < b m`) with `n` rows and columns indexed by `Tail n m`.
- `detPart h b m A y = ∏_j levelDet m (A j) y · ∏_j conj (levelDet m (B j) y)`.
- `gramPart h b dτ m y = (gramMinor m y)^{dτ_m - (h_m + b_m)/2}`, where `gramMinor m y` is the
  (real part of the) Gram determinant `det (Y_m Y_mᴴ)` of the rows `m, …, n-1` (Library,
  `ComplexDuality.GramWeight`).
- `levelProductExt h b dτ A y = ∏_m gramPart m y · detPart m (A m) y` and its restriction
  `levelProduct h b dτ A` to `GL_n(ℂ)`.
- `unitaryAct k A`: the level matrices `k A m j`, `k B m j`.

## Results

- `detPart_borel_mul`, `gramPart_borel_mul`, `levelProduct_borel_mul`: under left
  multiplication by `diag(a) u` (`u` upper unipotent) the level product is multiplied by
  `∏_m levelChar m h_m b_m dτ_m a`.
- `levelProduct_mem_principalSeries`: for characters `χ_k(z) = phase(z)^{l_k} |z|^{2 t_k}`, if the
  level data telescope, `∑_{m ≤ k} (h_m - b_m) = l_k` and
  `∑_{m ≤ k} dτ_m = t_k + (n-1)/2 - k`, then `levelProduct h b dτ A` lies in the smooth
  principal series `principalSeries ℂ n χ`. Smoothness holds because `gramMinor` is positive
  on units; the equivariance follows from `prod_levelChar`, the shift `(n-1)/2 - k` accounting
  for the normalization `|a_k|^{(n-1)-2k}` of the Library's principal series.
- `levelProduct_mul_unitary`: for `k ∈ U(n)`, `levelProduct A (g k) = levelProduct (unitaryAct k A) g`
  (the Gram determinants are `U(n)`-invariant and `levelDet_mul`).

## Provenance

Internal infrastructure for the growth bound `ComplexLinkedSmallGrowthStatement`,
one of the two growth statements of the dimension-count route to
`ComplexLinkedLanglandsQuotientNotLargeStatement` in the Library module
`ComplexLinkedLanglandsQuotientGrowth`; see `ComplexLinkedSmallGrowthProof.md` for how the pieces
fit together. This route is an independent internal proof, not taken from the literature. The
module introduces no statement from the literature, and all its results are proved here.
