# The lower unipotent form of a strict complex swap chart

`StrictSwapChain.permutation` is the permutation carrying final positions back
to initial positions. `chartProduct_zero` identifies the chart product at
zero with its permutation matrix.

If the source list is in Langlands order, the strict adjacent exponent
inequality at each step implies that the original label of the left position
is smaller than that of the right position. Moving the permutation matrices
in the chart product to the right conjugates each transvection into a lower
root subgroup. The proof of `chartProduct_mul_permutation_inv_mem_lower`
keeps the prefix permutation in the induction and uses the lower unipotent
entry criterion and subgroup multiplication.

The normal form is an internal matrix computation for the archimedean
constituent step in Getz and Hahn, *An Introduction to Automorphic
Representations* (2024), Theorem 10.6.4, printed p. 286 (PDF p. 298 of
`getz-hahn-2024-automorphic-representations`).
