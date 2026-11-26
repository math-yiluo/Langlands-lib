# Matrix entries of the real two-block Haar coordinates

`RealTwoBlockEntriesStatement`: the diagonal factor `diagonalBlocks g₁ g₂` of the two-block
chart is the standard consecutive block sum `blockSum (g₁, g₂)`, reindexed along `k + (n-k) = n`.
`realTwoBlockEntries` proves it by comparing the indices of the block shape with the two
summands of the standard finite sum of indices.

Consequences:

* `diagonalBlocks_eq_padGL`: `diag(g, 1)` is the padding `padGL g` used in the unequal-rank
  integrands;
* `determinant_diagonalBlocks`: `det diag(g₁, g₂) = det g₁ · det g₂`;
* `inverseTranspose_diagonalBlocks`: inverse transpose acts blockwise;
* `lastRow_diagonalBlocks_mul`: left multiplication by `diag(g, 1)` preserves the last row.

This is the real counterpart of the Library's `ComplexTwoBlockEntries`, used with the two-block
coordinates of Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §10.1.
