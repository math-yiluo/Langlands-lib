# Reordering the blocks of a finite cuspidal datum

Module `Langlands.BushnellKutzko.SplitTypeJacquet.FiniteReorder`.

`permuteShape B σ` lists the blocks of a block shape `B` in the order given by a permutation
`σ` of the block indices, and `permuteDatum E σ` does the same for a Harish–Chandra datum.
`permuteDatum_blockLabel` and `permuteDatum_labels`: the labels are permuted, so the label
multiset is unchanged.

`exists_permute_separated`: if a datum has two different block labels, there are a permutation
`σ` of the blocks and a cut `j` with `0 < j` and `j` less than the number of blocks such that the
label sets on the two sides of the cut are disjoint: `E.blockLabel (σ i) ≠ E.blockLabel (σ i')`
whenever `i < j ≤ i'`. This separation is all that the statement exports. The witness is
constructed by choosing a label `ℓ` that occurs and sending the first `j` indices onto the blocks
labelled `ℓ` (counted by a `Finset.filter`) and the remaining indices onto the others, so in the
witness the first `j` blocks all carry `ℓ`.

`finrank_parabolicHom_eq_of_labels_eq`: for two data `E`, `E'` with the same label multiset and
a finite-dimensional representation `X` of `GL_n(k)`, the spaces of `P`-equivariant maps from the
inflated Levi tensor of `E`, respectively `E'`, into the restriction of `X` have the same
dimension. By Frobenius reciprocity (`finrank_intertwiningMap_induceRep_left`) both are
intertwining dimensions from the Harish–Chandra inductions; these are sums of products of
constituent multiplicities (`finrank_intertwiningMap_eq_sum_constituentMultiplicity`), and the
multiplicities of the two inductions agree (`constituentMultiplicity_eq_of_labels_eq`).
