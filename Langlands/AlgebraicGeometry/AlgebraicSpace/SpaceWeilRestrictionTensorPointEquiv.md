# Tensor Weil point equivalence over finite products of arbitrary rings

This internal supporting construction proves bijectivity of the original
tensor factor map without requiring the factors to be fields. It applies
in particular to finite families of completed valuation rings.

For a commutative ring `B`, an algebraic space `X` over `Spec B`, and a finite
family of commutative `B`-algebras `D i`, `finiteProductRingPointsEquiv`
identifies `X(product D i)` with the product of the `X(D i)`. Its forward
components are coefficient change along the original evaluation maps
`Pi.evalAlgHom`. The finite coproduct theorem for spectra gives a coproduct
with these actual spectrum projections. The published
`FppfCoproduct.sectionsEquiv` then applies the fppf sheaf condition of `X`.
The construction includes an empty index type and imposes no separation
or finiteness condition on `X`.

Let `R`, `B`, and `C` be commutative rings with the specified `R`-algebra
structures on `B` and `C`, and give each `D i` its specified `C`-algebra
and `B`-algebra structures. A supplied `C`-algebra equivalence
`C tensor_R B` with the product of the `D i` must send `1 tensor b` to the
original image of `b` in every factor. For `X` over `B`, assume explicitly
that its `R`-Weil restriction is algebraic.

`completedTensorSpaceWeilRestrictionPointsEquiv` composes the published
original-coefficient tensor point equivalence with
`finiteProductRingPointsEquiv`. Its component formula is exactly
`completedTensorSpaceWeilRestrictionPointMap`, by the published formula
for that map. Consequently the original factor map is bijective.

The provenance is internal composition of the existing tensor point
comparison, the actual finite coproduct of spectra, and fppf sheaf
gluing. No topology, representability theorem, or adelic endpoint is
claimed; algebraicity of the original Weil restriction remains a premise.
