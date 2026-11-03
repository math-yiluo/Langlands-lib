# Ordered products in central extensions of groups

This internal algebraic module isolates the group calculation in the final
central-extension step of CGP Theorem 3.3.11, *Pseudo-reductive Groups*,
second edition (2015), printed pp.115–116 (PDF pp.141–142), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`.

`orderedProduct` multiplies a finite family of images in `Fin n` order.
`map_orderedProduct` preserves that order under a target homomorphism.
`orderedProduct_mul_of_central` moves central correction factors to the
right while retaining the orders of both finite lists.

`injective_of_quotient_and_kernel` assumes uniqueness of ordered quotient
coordinates and uniqueness for tuples mapping to the identity under the
factor quotient maps. For two tuples with the same product, their quotient
coordinates agree; their componentwise differences lie in the kernels.
Centrality moves those differences through the product, after which kernel
uniqueness identifies each component.

`exists_of_lifts_and_kernel` starts with a tuple whose product has the desired
quotient image. The discrepancy from the desired element lies in the target
kernel. A tuple factoring that discrepancy corrects the original tuple.
Centrality again permits the ordered product calculation.

These results make no assertion that the quotient maps are surjective on the
original groups. In the scheme application the tuple of lifts will be obtained
after an fppf change of test scheme. This module proves no geometric
representability or semigroup realization result.
