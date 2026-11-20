# Separation of normalized parameters by the Gelfand recursion

This internal lemma uses the diagonal Gelfand polynomials from
`ComplexJacquetFinite`. Subtracting the coordinate index from the input
absorbs the index term of their recursion into the normalized parameter
`bᵢ`. The generating series `Gᵢ` of the diagonal values satisfies
`(1 − bᵢT) Gᵢ = 1 − T ∑_{j < i} Gⱼ`.
Multiplication over successive initial segments turns this into

`(1 − T ∑ᵢ Gᵢ) ∏ᵢ (1 − bᵢT) = ∏ᵢ (1 − (bᵢ + 1)T)`.

If two parameter lists have the same sums of diagonal values at every
degree, cross multiplication equates the corresponding polynomial
products. Evaluation at `T = 1/z`, with `z ≠ 0`, gives
`P_b(z − 1) P_c(z) = P_c(z − 1) P_b(z)`, where `P_b` and `P_c` are the
monic root polynomials. At a sufficiently large real point and its
successive integer translates, `P_c` is nonzero and the ratio of the
polynomials is constant. Infinitely many roots force the cross-scaled
difference to vanish. Monicity gives equality of the polynomials, so
their root multisets, including multiplicities, agree.
