# Actual pointed commutator image pullback and augmentation tensors

This internal adapter uses the actual closed commutator image, its restricted
pointed action, and the actual componentwise action on the two input schemes.
Over any field and at an arbitrary universe, the product-to-image factor
preserves the action and the distinguished rational point. Its already proved
injective coordinate pullback therefore transports augmentation support from
the image to the product. Both identity slices of the factor are the constant
image origin.

For arbitrary pointed affine schemes, the module identifies pullback along a
constant rational point with evaluation at that point. It then identifies the
two standard coordinate identity-slice maps, under the actual product
coordinate equivalence, with pullback along the actual pointed slices.
Specializing these identities to the commutator image proves that its
augmentation ideal pulls back into the tensor product of the two input
augmentation kernels. The tensor product uses one augmentation kernel from
each factor; no constant summand is added.

`imageAugmentationPullback` gives the canonical linear factor into this tensor
of kernels by applying the two scalar-subtraction projections.
`imageAugmentationPullback_include` proves that including its value in the
full coordinate tensor recovers the actual image-factor pullback.

The equivariance proof compares the two product projections and then applies
the existing all-test factor-equivariance identity. The point identity is
definitional. Support transport applies the published injective-pullback
theorem. Each identity-slice proof cancels the closed image inclusion and uses
the actual commutator formula. The coordinate slice identities are checked on
pure tensors using the product-projection pullback identities. The final
augmentation inclusion applies the published theorem that simultaneous
vanishing on the two identity slices is precisely membership in the range of
the tensor of the two augmentation-kernel inclusions. The canonical factor
uses the already proved projection identity for elements vanishing on both
slices.

The image and tensor steps are motivated by Conrad–Gabber–Prasad,
*Pseudo-reductive Groups*, second edition (2015), Lemma 3.3.4, printed
pp.108–109 / PDF pp.134–135. These are internal affine-scheme derivations,
without a claim of the source's full weight-sum theorem. No decomposition,
integrality, or generated-subgroup result is established here.
