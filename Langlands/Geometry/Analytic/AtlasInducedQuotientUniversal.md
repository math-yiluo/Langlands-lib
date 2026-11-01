# Relative universal property of arbitrary-atlas quotient induction

Author: Worker 56. Namespace: `Langlands.Analytic.AtlasInducedAction`.

This internal construction transports the relative universal property of
arbitrary-atlas coset-copy induction to the actual balanced quotient.
Let `K : Type u` be a complete normed ultrametric field, `G : Type z`
a topological group, and `H` an open subgroup. Source and target
presentations lie in `AffinoidAtlasPresentation.{u, max z v, max z w} K`.
The subgroup source action `X` has the specific jointly continuous point
action `ContinuousSMul H (LocalSpace H X)`. The target `Y` is any supplied
categorical `G`-action: no joint continuity of its point action is needed.
For source naturality the second source action has the same continuity
condition. Original charts may overlap, nest or be empty; empty spaces,
empty chart-index types and infinite index of `H` are allowed.

Given a full subgroup-equivariant arrow `f` from `normalizedAction H X`
to the restriction of `Y`, `quotientExtendMap` is the actual inverse
copies isomorphism followed by the existing constructed `extendMap`.
The corresponding composite in the action category constructs
`quotientExtendToAction`; its commutation equation proves full bounded
equivariance. The normalized quotient-unit triangle follows by cancellation
of the copies isomorphism and the existing complete unit-extension triangle.

`quotientRestrictFromAction` first precomposes an arbitrary full quotient
arrow with the equivariant copies isomorphism, then uses the existing
restriction correspondence. Its underlying bounded arrow is exactly
composition with `quotientUnitMap`, by associativity.
The two inverse laws follow from the corresponding coset-copy inverse laws
and cancellation of the constructed equivariant isomorphism.
`quotientActionExtensionEquiv` packages
`Hom_G(action H X hH,Y) ≃ Hom_H(normalizedAction H X,Res Y)`.
Its injectivity gives uniqueness from agreement after the full normalized
quotient unit.

The correspondence is natural in every original full equivariant source
arrow, using the complete quotient-unit naturality, and in every full
equivariant target arrow, using associativity. Applying injectivity and
the inverse laws proves the corresponding naturality equations for the
constructed extension.

Transport leaves the chosen index equal to the index of `f` followed by
the target action at the coset representative. Its bounded pullback is
precisely the contravariant composite of those two supplied maps:
the source transport's bounded identity pullback cancels.
Evaluating the full unit triangle gives the value at `[1,x]`.
Every representative is the translate `g • [1,x]`; point evaluation of
complete equivariance and the existing exact quotient action realization
therefore prove `[g,x] ↦ (Y.ρ g).baseMap (f.hom.baseMap x)` for arbitrary `g`.

The provenance is internal categorical transport of the constructed
arbitrary-atlas relative extension, rather than an additional assumed
universal property. No output extension, inverse normalization or
faithfulness of spectrum points on bounded maps is assumed. Every
whole-arrow claim is proved before point evaluation. The right-hand Hom
starts at the original same-space nonempty-chart normalization; this is
not an identity-source adjunction on all chosen atlas presentations.
An explicit nonempty-chart adjunction, analytic automorphism continuity,
refinement localization, general analytic sites and Harris tower
specialization remain separate obligations.
