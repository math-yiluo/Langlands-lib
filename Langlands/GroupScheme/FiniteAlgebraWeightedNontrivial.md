# Detecting a nontrivial weighted cocharacter

This is an internal consequence of the published
`Langlands.GroupScheme.FiniteAlgebraWeightedDynamic` construction, used for the
split-rank lower bound in Task 5395. It needs no external structural theorem.

For an infinite field `k`, a nontrivial `k`-algebra `D`, a finite matrix index
`n`, and a supplied finite `k`-basis of `Matrix n n D`, the theorem
`FiniteAlgebraUnits.WeightedRoot.cocharacter_ne_zero_of_weight_eq_one` says
that the actual weighted diagonal cocharacter is nonzero whenever one of
its integer weights is one. There is no characteristic restriction.

The proof chooses `c` in `k` different from zero and one and evaluates at
the corresponding multiplicative-group point of the affine base test.
The relative affine-section comparison identifies its coefficient algebra
`R` with `k`. Tensoring that comparison and applying the tensor-unit
equivalence identifies `R ⊗[k] D` with `D`, so it is nontrivial and its
scalar map from `k` is injective. The published all-test tensor-matrix
comparison gives `c` in the indicated diagonal entry. If the cocharacter
were zero, that entry would be one, contradicting the choice of `c`.

`nontrivialCocharacterOfWeightOne` packages that actual weighted cocharacter
and its nonzeroness certificate in a subtype.

This module detects nontriviality in the full matrix-algebra unit group.
Its quaternionic application also requires the separately constructed
factorization through the reduced-norm-one isometry group and transport
from a hyperbolic normal form.
