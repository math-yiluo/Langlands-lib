# Block special unitary matrices for an adjoined line

Module: `Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisStabilizer`.

For `H = adjoinSkewLine H₁ c₀` (the orthogonal sum of `H₁` and the line `⟨c₀⟩` in the last
coordinate):

- `blockUnit R v = adjoinSkewLine v 1` embeds units of size `m` in units of size `m + 1`;
  `blockUnit_injective`, `unitMap_blockUnit`, and `blockUnit_mem_iff`
  (`blockUnit v ∈ suGroup τ H R ↔ v ∈ suGroup τ H₁ R`, using
  `matrixReducedNorm_adjoinSkewLine_one`).
- `lastRow R` is the last standard row vector; `exists_blockUnit_of_fix` (`c₀` a unit): a
  special unitary matrix for `H` fixing the last row is a block unit. This is the stabilizer
  computation `adjoinSkewLine_fix_last_iff` of `SkewLineStabilizer`.
- `IsCrossed.twist`: `s ↦ u * c s * s(u)⁻¹` is again a crossed homomorphism.
  `exists_block_cocycle`: if every twisted value fixes the last row, the twisted crossed
  homomorphism is `blockUnit ∘ c₁` for a crossed homomorphism `c₁` with values in
  `suGroup τ H₁ L`. `exists_coboundary_of_block`: a special unitary primitive of `c₁` gives
  one of `c`.
- `ProperWittAt τ K N` is the proposition of proper Witt transitivity over `K ⊗ D` in rank
  `N`: for an invertible antihermitian Gram matrix `G` over `K ⊗ D` and rows `x, y` with
  `h(x, x) = h(y, y)` a unit, some isometry of `G` of reduced norm one maps `x` to `y`
  (Kneser, *Lectures on Galois Cohomology of Classical Groups* (TIFR Lectures on Mathematics
  47, 1969), §2.6, Lemma 2, printed pp. 32–33: for a nonsingular skew-hermitian matrix over a
  quaternion algebra, two rows with the same invertible value are related by a proper unitary
  matrix; over a division algebra a nonzero value is invertible, and in the split case the
  invertibility of the common value is needed).
