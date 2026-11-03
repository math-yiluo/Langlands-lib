# Augmentation support of actual pointed products

This internal adapter bounds the augmentation support of the actual product of
two pointed affine schemes with actions of the same commutative group scheme.
The product action and the all-algebra eigenconditions are the published
constructions. It is derived from the identity-slice argument in CGP,
*Pseudo-reductive groups*, second edition (2015), Lemma 3.3.4, printed
pp. 108–109 (PDF pp. 134–135). The extension from the mixed augmentation tensor
to arbitrary product augmentation is an internal deduction.

`PointedAction.leftSlice` and `PointedAction.rightSlice` are the actual
embeddings obtained by holding one coordinate at its distinguished point.
They preserve the origins and are equivariant on every test scheme.

`product_support_subset` assumes the explicit internal decompositions of both
factor augmentation modules and of the product coordinate algebra. It bounds
product augmentation support by the union of the two factor supports and their
literal pairwise sum. For a nonzero augmentation eigenfunction, a nonzero
identity-slice pullback witnesses the same character in the corresponding
factor augmentation. If both slices vanish, the published tensor-coordinate
slice identities and `weight_mem_sum_of_identity_slices` put the character in
the literal sum.

`product_support_subset_semigroup` uses closure under addition to preserve any
additive subsemigroup containing the two factor supports.
`product_support_subset_semigroup_of_split` obtains all three decompositions
from the published split-torus decomposition theorem. Neither result inserts
the zero character or assumes that the chosen subsemigroup contains zero.
The statements retain arbitrary fields and universe `u`.

This pair does not establish generated-envelope support, any geometric
generation assertion, or the host `SemigroupCommutatorStatement`.
