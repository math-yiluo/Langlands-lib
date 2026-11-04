# Dominance after residue-field scalar extension

This internal prerequisite constructs the actual restriction of a product
morphism to a residue fiber with both source and target extended to the same
residue field. It works over every field in universe `u` and uses the full group
algebra of the finite diagonalizable factor, including any nilpotents.

`residueFiberMorphism` takes a morphism `p : X × D(A) → Y` over `k` and a prime
`P` of `k[A]`. Its source is the actual scalar extension `X_κ(P)` and its target
is `Y_κ(P)`. The morphism is the pullback lift of the previously constructed
residue-fiber inclusion followed by `p`, together with the projection to
`Spec κ(P)`. The theorem `residueFiberMorphism_fst` identifies its composition
with the target projection with that original residue-fiber restriction.
The construction itself does not require `A` finite or either scheme affine.

For finite `A`, affine `X` and `Y`, geometrically integral `Y` over `k`, and
dominant `p`, `exists_isDominant_residueFiberMorphism` proves that this actual
morphism is dominant for some prime `P`. The finite closed-cover argument in
`FiniteDiagonalizableFibers` first selects a fiber dominant into the original
`Y`. Its residue field is finite over `k` by `FiniteDiagonalizableResidues`,
so `Y_κ(P) → Y` is finite and therefore integral. Geometric integrality makes
both `Y` and `Y_κ(P)` integral. The cancellation lemma described below then
proves dominance into `Y_κ(P)` itself. The imported residue-field result also
makes `κ(P)/k` separable, without restricting the characteristic or requiring
`k` perfect.

The general lemma `isDominant_of_comp_integral` treats affine schemes
`X → Y → Z` with `Y` and `Z` integral and the second map integral. Dominance of
the composite gives injectivity on global sections because `Z` is reduced.
The kernel of the first map on global sections contracts to zero in the
coordinate domain of `Z`. Since the coordinate domain of `Y` is integral over
that of `Z`, Mathlib's `Ideal.eq_bot_of_under_eq_bot` makes that kernel zero.
Injectivity on global sections implies dominance of the first map. This proves
the required cancellation using the actual morphisms and their coordinate maps.

The provenance is internal: the morphism is a categorical pullback lift, and
the dominance result combines the preceding residue-fiber constructions with
Mathlib's finite-morphism, geometric-integrality, schematic-dominance and
integral ideal-contraction results. No external geometric assertion is assumed.
Pointed split-torus extraction and the full rational maximal-torus conjugacy
statement remain separate proof obligations.
