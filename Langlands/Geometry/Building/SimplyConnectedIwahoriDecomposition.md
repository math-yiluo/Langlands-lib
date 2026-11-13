# Iwahori decomposition for a simply connected ambient group

`SimplyConnectedIwahoriDecompositionStatement.{u}` asserts the full predicate
`P.HasIwahoriDecomposition` for every supplied `ParahoricBuildingData G` over a
nonarchimedean local field of arbitrary universe, assuming
`P.SatisfiesApartmentAxioms` and algebraic `IsSimplyConnected G`. The theorem
`simplyConnectedIwahoriDecomposition` proves this statement.

The conclusion retains every chamber of the supplied apartment and every
generic cocharacter of the supplied maximal split torus. It includes all five
fields of `IsIwahoriDecompositionAt`: injectivity and the specified image of the
positive/central/negative product, existence of the least nonnegative affine
functionals, and the two ordered root-product assertions for every injective
enumeration of the non-divisible roots of the required sign. All factors are
the existing actual root groups and centralizer-zero subgroup.

The local theorem `hasIwahoriDecomposition_of_isSimplyConnected` applies the
published
`ParahoricBuildingData.isIwahoriDecompositionAt_of_forall_mem_normalizerZero`
to each chamber and generic cocharacter. Its only additional input is that a
normalizer point in `P.normalizerZeroComponent` preserving that chamber lies in
`P.normalizerZero`. The published theorem
`mem_normalizerZero_of_stabilizes_chamber_of_isSimplyConnected` supplies this
input from the same apartment axioms and `IsSimplyConnected G`. The global
theorem introduces the field, group, datum and two hypotheses, then applies the
local theorem.

This is derived content obtained by composing the named Library theorems in
`IwahoriDecompositionAxiomReduction` and `SimplyConnectedChamberNormalizer`.
It makes no new translation from the literature and asserts no existence of
building data. The explicit restriction on the ambient group is essential to
this result. The general reductive
`IwahoriDecompositionAxiomStatement` remains open; this supporting statement
does not discharge that target or its missing general normalizer-image theorem.
