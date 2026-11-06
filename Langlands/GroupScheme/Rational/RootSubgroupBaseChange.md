# Actual character-orbit root subgroups and arbitrary base change

This internal construction uses the existing relative root subgroup functor,
including its entire character-orbit extension and identity value at zero.
For arbitrary base schemes and an arbitrary base morphism it compares this
functor after actual scheme pullback with its original value on a test scheme
regarded over the original base. It does not assume that the character is a
root, that the torus is split, or that the group is reductive.

The projection formula compares the product with the entire commutative
acting group. Character evaluation is unchanged by pullback. Together with
the existing affine-line comparison this identifies both the orbit extension
equation and its identity value at zero. Existence in both directions gives
equality of the actual subgroup functors. The final multiplicative equivalence
uses exactly the existing baseChangePointsEquiv on ambient points.

The proof adapts the published Dynamic.BaseChange categorical comparisons to
the intrinsic character-orbit root subgroup definition. This is internal
provenance and asserts no additional theorem from original literature.
It supplies no root-valuation existence or filtration comparison, no enlargement
to a maximal split torus, no apartment map, and no supplied-model building
comparison. Those construction obligations remain open.
