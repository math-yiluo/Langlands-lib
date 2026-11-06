# Euclidean metric on a supplied valuation apartment

This module constructs a Euclidean metric on the original apartment of supplied
valuation building data. It is a first construction towards the building metric,
not a metric on the whole quotient.

The coordinates of a reduced translation vector are its evaluations under all
actual relative roots. The common kernel of these evaluations is precisely the
subspace divided out in `TranslationSpace`. The resulting linear map to the
finite Euclidean space indexed by the relative roots is therefore injective.
Pulling back its norm and inner product gives a real inner product space on the
existing translation quotient. Its squared norm is the sum of the squared root
coordinates. The embedding also proves finite dimensionality and hence
completeness.

The normalizer acts contragrediently on root evaluations. Its action consequently
permutes the finite sum of squares, so it preserves the constructed norm.
The affine displacement on the original apartment gives its metric; the existing
affine normalizer action preserves that metric. Choosing an origin identifies the
apartment isometrically with its translation space. This proves completeness and
the Library's midpoint nonpositive-curvature predicate on the apartment.
The empty root set is included: the common-kernel quotient is then zero.

The construction is an internal choice of a Weyl-invariant Euclidean metric of
the kind used at the beginning of Kaletha–Prasad (2023), Section 4.2, printed
p.168 / PDF p.199, read with the corrections of 1 November 2024, PDF pp.28–29.
The use of all actual root evaluations is independently derived; the source
allows any Weyl-invariant Euclidean normalization. Actual root finiteness comes
from the published Lie weight-support finiteness theorem for split tori, using
the smoothness of the reductive group to obtain locally finite type.

No building axiom is discharged here. Apartment-distance independence, a metric
on the building quotient, the global isometric action, global NPC and global
completeness remain obligations of `MetricRealizationStatement`.

Author: Worker 1688.
