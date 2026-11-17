# Restriction compatibility of actual identity cotangent sections

Let `G` be a smooth affine group scheme over an arbitrary base scheme
`S`. For each affine base open `U`, the earlier module
`IdentityCotangentSections` constructs

`sectionsEquiv G hG U :
  Γ(G.cotangentAtIdentity,U) ≃ (ker (IdentityJet.augmentation G U)).Cotangent`

as an equivalence linear over `Γ(S,U)`.
This module proves its compatibility with inclusion of affine base
opens and identifies the corresponding restriction on augmentation
classes. There is no noetherian, field or constant-rank hypothesis.

`differentialSectionsEquiv_inv_D` first proves that the inverse
algebraic differential model takes `d(a)` to the actual relative
derivation section of `a`. It applies the generic inverse-generator
formula from `RelativeDifferentialsAffineSectionGenerators` and
transports the equality of the `appLE` and actual structure-map algebra
structures.

`identityDifferential` sends a group function to the cotangent section
corresponding to its augmentation class under `sectionsEquiv`.
`identityDifferential_apply` proves that it is exactly the actual
pullback along the identity of the actual relative derivation section.
Thus this definition is tied to the actual differential map.

`functionRestriction G h` is restriction of actual functions above an
inclusion `h : V ≤ U` of affine base opens.
`identityDifferential_restrict` proves that the identity differential
commutes with these restrictions. The proof combines restriction of
section pullback, pullback of restricted sections, and naturality of
the actual relative derivation.

`restriction G hG h` is the semilinear map on actual augmentation
cotangents obtained by transporting the actual cotangent sheaf
restriction through the two section equivalences. Its coefficient
homomorphism is the actual structure-sheaf restriction
`Γ(S,U) → Γ(S,V)`.
`sectionsEquiv_restrict` states the resulting commuting square on
all actual cotangent sections.

The additional theorem `restriction_classMap` computes this map:
it sends `AugmentedAlgebra.classMap ε_U a` to
`AugmentedAlgebra.classMap ε_V (functionRestriction G h a)`.
Its proof uses the actual differential restriction computation.
`restriction_unique` proves that this formula uniquely determines
the semilinear restriction map, using surjectivity of the actual
ideal-class map. Hence the transported restriction has the intrinsic
augmentation-class meaning, beyond the commuting square supplied by
its definition.

These results are an internal continuation of the canonical affine
cotangent comparison and actual section-pullback formulas. No external
source claim, determinant-line isomorphism or group-isomorphism/base-change
comparison is added in this module.
