# Actual contragredients and finite-index induction

This module constructs the dual-induction comparison used in
`Langlands.VirtualRepresentation.ExactInductionDual`, which shows that exact
duality commutes with finite-index induction.

For a finite-dimensional representation of a finite-index subgroup,
`induceDualPairing` pairs its induced algebraic dual with its induced original
representation by summing pointwise evaluation over the actual right cosets.
The subgroup-equivariance and contragredient identities make pointwise
evaluation independent of the choice of coset representative. Right
multiplication permutes the finite coset set, so the sum is invariant under
simultaneous translation. This proves that the pairing is the intertwiner
`induceDualMap` into the full algebraic dual of induction.

Testing on an actual equivariant function with a single nonzero coset
coordinate recovers every coordinate of the dual-valued function. Hence the
pairing map is injective. The source and target have the same finite dimension:
induction multiplies dimension by subgroup index and duality preserves
dimension. The injective map is therefore the invertible intertwiner
`induceDualEquiv`.

All spaces and actions are the existing actual equivariant-function induction
and full algebraic dual, with independent coefficient, group and carrier
universes. The argument uses no equivariant splitting, semisimplicity,
finite-image condition or unproved project assertion.

This is internal derived finite-dimensional algebra. It claims no Fourier
equation, abelian epsilon identity, or generation theorem.
