# Compact Gram cutoffs for real Godement sections

A smooth cutoff of the row Gram matrix, supported in a compact set of invertible matrices, turns the normalized bottom-row representative of an upper real principal-series vector into a smooth Godement test with compact full-row-rank support. On the orthogonal subgroup its section is an integral of translates by the lower block matrices `diag(1,h)`.

Each squared entry of a rectangular matrix is at most the trace of its row Gram matrix. The trace is bounded on the compact Gram support, so its closed preimage lies in a compact cube. Inverting the Gram matrix gives a right inverse for each rectangle in the preimage. The test is smooth by the normalized descent formula on full-row-rank rectangles and is locally zero off the closed preimage.

The trailing rows of `diag(1,h) * g` are `(0,h)g`. Insert this identity into the normalized descent formula, then cancel the upper determinant factors using multiplicativity. The inside shift exceeds the outside shift by one half, leaving the factor `|det h|^(1/2)`. For orthogonal `g`, the Gram matrix of `(0,h)g` is `h * h.transpose`, so the cutoff in the integral is independent of `g`.

This is an auxiliary calculation for the generation argument in Hervé Jacquet, *Archimedean Rankin–Selberg Integrals*, Section 7.1, Proposition 7.1(v).
