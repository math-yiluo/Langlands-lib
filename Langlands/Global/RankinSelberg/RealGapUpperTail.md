# Upper block matrices in the real split tail

This module is the real counterpart of the Library's `ComplexGapUpperTail`; the statements and
proofs are the field-independent block calculations of the complex module, over `ℝ`.

`packedTail k q Y Z` is the upper unipotent matrix in `N_{k+q+1}(ℝ)` with identity leading block,
upper right block the `k × (q + 1)` rectangle `Y` and lower right block `Z ∈ N_{q+1}(ℝ)`
(`packedTail_top_left`, `packedTail_top_right`, `packedTail_bottom_left`,
`packedTail_bottom_right` give its blocks).

* `packedTail_mul`: `packedTail X Z · packedTail Y T = packedTail (Y + X T) (Z T)`.
* `packedTail_conj`: conjugation by the embedded `g ∈ GL_k(ℝ)` replaces `Y` by `g Y` and fixes `Z`.
* `firstRectangle x` and `laterRectangle X` place a column in the first slot, respectively a `k × q`
  rectangle in the later slots, of the upper right block.

`RealGapUpperTailStatement` (proved by `realGapUpperTail`) collects four facts:

1. `packedTail Y Z = packedTail (firstRectangle (first column of Y)) 1 ·
   packedTail (laterRectangle (later columns of Y − firstRowCorrection)) Z`, the factorization matching
   `splitTailRectangle`;
2. for a rectangle supported in the later columns, the sum of the simple-root entries of
   `packedTail` equals that of the tail `Z`;
3. the later physical columns of `packedTail (laterRectangle X) Z` are the vectors
   `directColumn k q X Z j`;
4. the preceding columns of the transpose of `packedTail 0 Z` are the vectors
   `transposeColumn k q Z j`.

The proofs compute with the consecutive block decomposition `Fin k ⊕ Fin (q + 1) ≃ Fin (k + q + 1)`.
[Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.2, Lemma 10.2](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
