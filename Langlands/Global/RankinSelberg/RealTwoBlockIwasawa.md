# Logarithmic Iwasawa coordinates in the right-tail chart

`alpha` is the logarithmic diagonal Iwasawa coordinate of `RealIwasawa`.

* `blockLog y z` concatenates coordinate vectors of the two blocks.
* `alpha_diagonalBlocks`: `alpha (diag(g₁, g₂)) = blockLog (alpha g₁) (alpha g₂)`. The proof embeds
  the upper unipotent factors and the orthogonal factors of the two Iwasawa decompositions
  blockwise (block sums of orthogonal matrices are orthogonal, block sums of upper unipotent
  matrices are upper unipotent) and identifies the diagonal factor entry by entry.
* `upperRectangle_mem_upperUnipotent`: the upper rectangle is upper unipotent.

`RealTwoBlockIwasawaStatement`: for `g ∈ GL_k(ℝ)`, `h ∈ GL_{n-k}(ℝ)`, a rectangle `X` and an
orthogonal `q`,

`alpha (padGL g · (rightTail h X q)⁻¹) = blockLog (alpha g) (alpha h⁻¹)`.

`realTwoBlockIwasawa` proves it: conjugating the inverse rectangle by `diag(g, 1)` gives an upper
unipotent matrix, `alpha` is invariant under left multiplication by upper unipotent matrices and
under right multiplication by orthogonal matrices (`alpha_unipotent_mul`, `alpha_mul_orthogonal`),
and the remaining factor is `diag(g, h⁻¹)`.

This is the real counterpart of the Library's `ComplexTwoBlockIwasawa`; it controls the Whittaker
argument of the restriction kernel in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009),
§10.3.
