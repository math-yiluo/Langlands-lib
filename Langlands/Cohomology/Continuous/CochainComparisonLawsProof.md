# Canonical discrete cochain comparison and naturality

Author: Worker 54. Task `3e5bcb49-74aa-43fe-9bb0-df08f248dc4a`, revision 1.

The theorem `Langlands.Continuous.cochainComparisonLaws` proves exactly the
published proposition `Langlands.Continuous.CochainComparisonLaws`. It imports
`Langlands.Cohomology.Continuous.CochainComparisonLawsStatement` unchanged.
The theorem has arbitrary universe parameter `u`, with no additional outer
parameters or hypotheses. A final unapplied-constant assignment checks this
signature directly.

For a discrete topological group, the actual canonical comparison is an
isomorphism of cochain complexes, each component is an isomorphism, and the
induced comparison on actual cohomology is an isomorphism in every natural
degree. The coefficients need not be discrete and the group need not be finite.
For arbitrary topological groups, the canonical comparison commutes with the
published Mathlib change-of-group and coefficient maps, both on cochains and
on cohomology.

The proof uses the existing nested continuous homogeneous cochains throughout.
`nestedEval_injective` proves by induction that evaluation at all finite tuples
detects equality. At the successor step, equality of continuous functions is
reduced to equality of their values, followed by the induction hypothesis.
This part needs no discreteness.

For a discrete group, `nestedLift` recursively converts an arbitrary tuple
function into a nested continuous function. Every outer function is continuous
because its domain is discrete. `nestedEval_lift` proves that evaluation
recovers the original function, using the unique empty tuple in degree zero
and the decomposition of a tuple into its head and tail in the successor case.
A covariant function lifts to an invariant nested cochain: evaluation
injectivity reduces invariance to the published `nestedEval_action` formula
and the covariance identity. Composing this bijection with the published
`covariantHomEquiv` proves `homogeneousTermMap_bijective`.

In `ModuleCat`, bijective morphisms are isomorphisms. Thus the homogeneous
comparison is componentwise invertible and hence an isomorphism of complexes.
Its composite with `standardToInhomogeneousIso` remains invertible, as does
each component. The homology functor and the inverse forgetful-functor
homology isomorphism give invertibility of `continuousToOrdinary`.

Naturality is checked for the selected canonical map, using the formula
`continuousToOrdinaryCochains_apply`: on an inhomogeneous tuple
`(g₁, …, gₙ)`, the comparison evaluates the nested cochain at
`(1, g₁, g₁g₂, …, g₁⋯gₙ)`. The auxiliary
`diagonalSuccIsoFree_inv_single` unfolds the standard-to-bar representation
isomorphism on a free generator. It uses the tensor-product and linearization
formulas, then `Action.diagonalSuccIsoTensorTrivial_inv_hom_apply`. The
argument is adapted from the local generator calculation in Mathlib's
`Rep.barComplex.d_comp_diagonalSuccIsoFree_inv_eq`, in
`Mathlib/RepresentationTheory/Homological/Resolution.lean`.

`nestedEval_resolutionMap` proves by induction that the recursive continuous
change-of-group map evaluates as coefficient-map application after coordinatewise
precomposition by the group homomorphism. `map_partialProd` proves that partial
products commute with that homomorphism. Substitution in the comparison formula
proves `continuousToOrdinaryCochains_naturality` by extensionality, with no
discreteness hypothesis.

Finally, `continuousToOrdinary_naturality` applies
`ShortComplex.mapHomologyIso_inv_naturality` to the short complexes in the
chosen degree. Applying `HomologicalComplex.homologyMap` to the cochain square
and using preservation of composition gives the required cohomology square.
This accounts explicitly for the forgetful functor in the definition of the
canonical cohomology comparison.

These are derived implementation arguments for the already published statement
and canonical definitions; no new source assertion or replacement model is
introduced. The original mathematical provenance is documented in the imported
statement's Markdown: Serre, *Local Fields* (1979), Chapter VII Sections 3 and 5,
and Chapter X Section 3. The proof route above is the route implemented in Lean.

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
