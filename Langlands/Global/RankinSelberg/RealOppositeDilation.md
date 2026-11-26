# Diagonal contraction on the real opposite cell

For `ε > 0`, `contractionDiagonal n hε` is the diagonal matrix with entries `ε^i`
(`i = 0, …, n-1`). `contraction n hε` is conjugation of the upper unipotent group `N_n` by
the inverse of this diagonal (`contraction_val`); it multiplies the strictly upper entry
`(i, j)` by `ε^(j-i)` (`contraction_entry`). After transposition it is conjugation by the
diagonal itself on the lower unipotent matrices (`transpose_contraction`).

`contractionDegree n` is `Σ_{i<j} (j - i)`. Since each entry is one real coordinate, the
real Jacobian of the contraction is `ε^(contractionDegree n)`, so

* `map_contraction`: the pushforward of `realEntryLebesgue n` under the contraction is
  `(ε^(contractionDegree n))⁻¹` times `realEntryLebesgue n`.

The proof computes the scaling of the Lebesgue measure in each coordinate, takes the product
measure (`HarmonicAnalysis.pi_nnreal_smul`) and transports it through the upper-entry
homeomorphism.

`norm_transpose_contraction_sub_one`: for `ε ≤ 1` and the entrywise supremum norm,
`‖(contraction u)ᵀ - 1‖ ≤ ε ‖u - 1‖`, because each strictly upper entry is multiplied by a
positive power of `ε`, the diagonal entries stay one and the other entries stay zero.

`RealOppositeDilationStatement` collects the Jacobian identity, the transpose identity and
the displacement bound; `realOppositeDilation` proves it.

This is the real counterpart of the Library's `ComplexOppositeDilation` (where each entry is
two-dimensional and the exponent doubles). It is an internal change of variables, used with
the opposite-cell integration formula of `RealModulusOpenCell` in
`RealNormalizedCompactAverage`.
