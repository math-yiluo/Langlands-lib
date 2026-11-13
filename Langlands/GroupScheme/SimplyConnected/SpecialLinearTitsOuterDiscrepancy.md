# Outer discrepancies after trivialising the inner subgroup

Author: Worker 239.

This internal unit develops the actual all-test Galois discrepancy of a
local presentation from `SL_(n+1)` to a group scheme over an arbitrary
field `K`, on a cover `Spec L`. It uses the existing discrepancy
composition law and the inverse-transpose homomorphism `θ`.

`HasTrivialDiscrepancy E H` says that every element of the specified
automorphism subgroup `H` acts identically on every test scheme, cover
point, and determinant-one matrix. It introduces no descent or
classification assumption.

Two outer representatives `X` and `Y` compose to the inner representative
`X θ(σ(Y))`. Scalar multiplication preserves every outer action after
every cover coefficient homomorphism. Equal outer actions induce equal
conjugations on `SL(L)`: evaluate at the identity point of `Spec L`,
use its coefficient ring equivalence, and precompose the test matrix by
inverse transpose.

Right multiplication by an element of `H` leaves the discrepancy
unchanged. Therefore one outer representative works for every
automorphism in its left coset. If `H` is normal, comparison of `τσ`
and `σ(σ⁻¹τσ)` also proves independence under shifting the cover point
by `τ ∈ H`. Consequently, applying `τ` to every entry of an outer
representative leaves its all-test action unchanged.

If `σ² ∈ H`, composing an outer action with itself gives identity
discrepancy. The established centralizer calculation on the special
linear group then gives a unit scalar `b` such that
`X θ(σ(X)) = b I`.

These are internal consequences of the imported algebraic constructions.
The unit does not construct a cover or a trivialisation of its inner
subgroup, descend a matrix to a fixed field, or assert the final
Hermitian presentation.
