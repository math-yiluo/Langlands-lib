# Lie and compact identities of a restored Levi coefficient tensor

`IsRealizedLeviPeriodCoefficient` identifies the function given by evaluating the
tensor on the adelic Levi with the translated block period of `j w`, for every
source vector `w`. Holding all but one coordinate fixed identifies each tensor
slice with the corresponding finite-smooth block slice.

The compact and real block Lie identities also assume that `j` intertwines
the source action `A` with the translated-period operator action. This
intertwining identifies the period of the acted-on vector with the action
on the period. Under the same hypothesis, injectivity of product evaluation
transfers the vanishing of the period derivative in strictly upper block
directions to the coefficient tensor.

Tensoring the inverse determinant twist equivalences cancels the product
character of the weighted coefficient and gives `IsRealizedLeviPeriodCoefficient`.
The operator identities then apply with the intertwining hypothesis on `j`.
