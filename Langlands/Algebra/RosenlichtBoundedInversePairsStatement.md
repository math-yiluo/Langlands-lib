# Bounded normalized inverse pairs

`Langlands.Algebra.RosenlichtBoundedInversePairsStatement.{u,v}` asserts the
following internal prerequisite for the affine Rosenlicht tensor-units argument.
Let `k` be an algebraically closed field, `B` a commutative domain that is a
`k`-algebra, and `epsilon : B →ₐ[k] k` a chosen algebra homomorphism.
For finite-dimensional `k`-subspaces `V` and `W` of `B`, the set of pairs
`(b,c)` with `b ∈ V`, `c ∈ W`, `b * c = 1`, and
`epsilon b = epsilon c = 1` is finite.

The universes of `k` and `B` are independent. There is no finite-type
hypothesis on `B`. The finite-dimensional hypotheses use `Module.Finite`
on the submodule types. Finiteness is `Set.Finite` for the indicated subset
of the actual Cartesian product `B × B`.

This is an internally formulated supporting statement for Task 7474, not a
quotation or translation of a numbered result in the literature. Normalizing
both factors removes the scalar rescaling of inverse pairs. Applying the
statement to the finite-dimensional spaces containing the specializations
of a tensor unit and its inverse is the intended use. This file states the
prerequisite and does not prove it.
