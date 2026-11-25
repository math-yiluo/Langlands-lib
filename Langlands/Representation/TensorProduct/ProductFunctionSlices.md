# One-coordinate slices of tensors of functions

In a pure tensor, fix the arguments outside a distinguished coordinate.
The slice is the vector in that coordinate multiplied by the product of
the fixed values. This formula places the slice of every algebraic
tensor in the range of the distinguished coefficient evaluation.
Invert that evaluation on its range to obtain a linear map to the
factor carrier.

Applying an endomorphism to the distinguished factor applies that
endomorphism to every slice in that coordinate. Conversely, the
identity of those slices determines an identity of tensors whenever
all the factor evaluations are injective. A family of maps of the
factors intertwines the distinguished endomorphisms when its map in
that coordinate intertwines them.

This internal construction turns identities for individual Levi slices
into identities for the block operators on the coefficient tensor. It
allows the cuspidal direct-sum projections in the proof of
`CuspidalSupportExistenceStatement`
(`Langlands.Global.Factors.CuspidalSupportExistenceProof`) to retain those
operator identities.
