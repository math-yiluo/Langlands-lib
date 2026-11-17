# Simultaneous presentations on the actual common Levi

This internal construction assembles published group-scheme results for the
actual common-Levi continuation problem. It is a derived adapter, not an
additional claim from Waldspurger IV.1.1 and not a proof of analytic continuation.

`ParabolicData` contains one complete root presentation, its geometric radical,
the exact canonical Levi inclusion, and the three all-test `Realizes` equalities.
`parabolicData` uses `fixedLeviParabolicModel` to keep the canonical centralizer
scheme of χ as the Levi of the parabolic defined by ψ. The common-centralizer
equality supplies its centralizer representation. The canonical unipotent
representative is lifted into that parabolic by `Dynamic.unipotentToParabolic`.
`dynamicGeometricUnipotentRadical` and the affine comparison
`IsGeometricUnipotentRadical.leviSubgroup` prove its geometric-radical predicate.
`parabolicRootPresentationExistence` supplies the complete root presentation for
the specified parabolic, Levi and split component. Each realization field is the
range equality of the corresponding represented subgroup functor; none is only
an equality on rational points.

`commonData` first uses `parameterScheme_isConnectedReductive` and
`splitComponentStatement` to choose one split component of the canonical
centralizer. It then applies the preceding construction to ψ and ψ′ with that
same source and inclusion. Thus `CommonData.levi_comp` follows by transitivity
through the canonical centralizer morphism. No conjugacy choice or change of
Levi model is required.

`OppositeData` and `oppositeData` supply the represented dynamic parabolic and
geometric radical for any specified auxiliary cocharacter, including the
negative split-component cocharacter of the second presentation. They use
`Dynamic.affineDecompositionModel`, `dynamicGeometricUnipotentRadical` and the
same affine radical comparison. `parameterScheme_locallyOfFiniteType` inherits
local finite type from the closed centralizer inclusion.

The constructions work over arbitrary fields and retain nonsplit groups,
arbitrary characteristic and rank zero. No analytic or representation-theoretic
premise enters these constructions. Rational-point continuity, compact
factorizations and the final use of the independent IV.1.1 and presentation
reduction proofs are separate assembly obligations.
