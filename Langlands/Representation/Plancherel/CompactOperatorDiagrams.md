# Pointwise and compact-chart comparisons for linear operators

`isPolynomialOperatorOn_of_pointwise_regular_smul` turns a single regular multiplier shared by every evaluation into a globally polynomial operator. Joint injectivity of the evaluations gives the operator identity, and the constant-operator polynomiality theorem gives the conclusion. `pointwise_regular_smul_of_reparam` transports the value identity along a parameter map with the corresponding scalar evaluation.

`eval_linearEquiv_symm` derives the evaluation equation for the inverse of a linear equivalence. `compactOperatorOfSquare` inserts two chart equivalences around a commuting square of linear maps. Its proof cancels the charts and uses the original square before applying the final linear map.

`StandardIntertwining.inducedLeviLinearEquiv` equips `inducedMap` for an inducing equivalence with its inverse. The inverse is `inducedMap` for the inverse inducing equivalence. Checking both on the underlying functions gives the two inverse laws. This choice makes the forward map directly usable in `fullSourceIntertwiner_natural`.
