# Actual additive product formula in the mixed embedding

Worker 1692 derives this adapter from `HeckeProductFormula`,
`HeckeFunctionalEquationStatement` and the mixed-space trace in
`Hecke.MixedSpaceFourier`. It uses every supplied finite local additive
component and real or complex additive scale, with unrestricted universe `u`.
It assumes the original global character is trivial on the diagonal. It
assumes neither an adelic self-duality equivalence nor a conductor support
conclusion.

`mixedRealScale` and `mixedComplexScale` only reindex the supplied nonzero
unit-valued scale families by the real and complex place subtypes used in the
mixed space. Both resulting scalar families are nonzero at every place.

`infinite_additive_product_eq_mixed` splits the actual infinite-place product
into real and complex places. The supplied local component equalities identify
each factor. The chosen completion embeddings restrict to precisely the real
and complex embeddings used by Mathlib's mixed embedding. The real factors
are `𝐞(a_v x_v)` and the complex factors are `𝐞(2 Re(a_v x_v))`.
The additive character law combines them into `𝐞(addTrace aR aC x)`, with a
positive sign and the original factor two in the complex trace.

The full integral-product kernel from `HeckeProductFormula` also proves that
the actual finite restriction is one on every completed integer outside the
chosen integral control set. A single-coordinate integer family vanishes at
each controlled place, and its integral inclusion equals the actual local
inclusion.

`mixed_additive_product_formula` chooses the union of that control set and the
nonintegral places of a diagonal element. Every finite local component is one
outside this union. On the union, the earlier actual diagonal product formula,
the infinite-place comparison and the supplied finite component equalities give
`𝐞(addTrace aR aC (mixedEmbedding K x)) * ∏ v ∈ S, ψ_v(x) = 1`.
This is the mixed-space product formula needed in the arithmetic lattice
argument. Conductor support, local-data existence, Poisson summation, analytic
continuation and the global functional equation are separate conclusions.
