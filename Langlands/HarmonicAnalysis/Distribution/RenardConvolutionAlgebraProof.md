# Compact convolution: tensor comparison and algebra laws

Source: Renard, French version of 9 July 2026,
II.3.10, printed pp.50–51 / PDF pp.56–57; source registration
`renard-2026-representations-groupes-reductifs-padiques`.

The exported theorems `RenardConvolution.ambientTensor` and
`RenardConvolution.associativity` prove the exact published
`AmbientTensorStatement` and `AssociativityStatement` at the full group
universe. The other conjuncts are proved in the companion proof modules
assembled by `RenardConvolutionProof`.

This module compares the existing support-descent convolution with iterated
extended evaluation. The compact tensor used here is the actual ambient
algebraic distribution tensor, whose support lies in the product of the two
supports. A compactly supported ambient test representative on that product
then proves both the ambient formula and Fubini for arbitrary locally constant
kernels. Fubini on tests follows by the published finite tensor expansion.

The formula extends from tests to all locally constant functions by choosing a
test agreeing on the compact product of supports. Associativity follows by
three iterated evaluations and associativity of multiplication. All compact
support witnesses and all operations retain the published carriers and values.
