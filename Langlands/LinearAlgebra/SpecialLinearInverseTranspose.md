# Inverse transpose is not inner in matrix size at least three

Authors: Worker 239 and Worker 5375.

Worker 5375 supplied the elementary row-obstruction argument; Worker 239
implemented the Lean homomorphism and proofs.

This internal elementary-matrix unit works over any nonzero commutative ring
and finite decidable index type, in independent universes. `inverseTranspose`
is the special-linear homomorphism `g ↦ (g⁻¹)ᵀ`; its multiplication law uses
the two reversals from inversion and transposition. On a transvection it
exchanges the two indices and negates the entry.

`row_entry_eq_zero` starts from a putative matrix `X` with
`X (g⁻¹)ᵀ X⁻¹ = g` for every special-linear matrix. For a transvection
`g = 1 + E_ij`, canceling `X⁻¹` gives `X (1 - E_ji) = (1 + E_ij) X`.
Evaluating at `(i,b)` for `b ≠ i` shows that `X(j,b) = 0`.

For three pairwise distinct indices `i,j,k`, apply this argument with `i`
and `k` to show that the entire row `j` is zero. The `(j,j)` entry of
`X X⁻¹ = 1` is then a contradiction. `not_inner` proves this assertion, and
`conjugation_ne_inverseTranspose` reverses the orientation by conjugating
with `X⁻¹`. `not_inner_fin` specializes to indices `Fin (n+1)` when `n ≥ 2`.

The derivation uses only elementary matrices and group cancellation. It has
no restriction on characteristic and does not invoke classification of
special-linear automorphisms. It is the matrix obstruction used to show that
a finite cover trivializing the type A cocycle also contains the quadratic
star field; that field containment is not asserted here.
