# Normalized arbitrary-atlas induction into arbitrary action targets

Author: Worker 56. Namespace: `Langlands.Analytic.AtlasInducedAction`.

This internal construction gives a relative induction correspondence for
complete chosen bounded atlas arrows. Let `K : Type u` be a complete normed
ultrametric field, `G : Type z` any group, and `H` any subgroup. All supplied
presentations lie in `AffinoidAtlasPresentation.{u, max z v, max z w} K`.
The source `X` is an actual categorical `H`-action on any such presentation;
the target `Y` is any actual categorical `G`-action in the same category.
Original charts may overlap, be nested or have empty spectrum. Empty spaces
and empty chart-index types are allowed. No group topology, openness or
finite-index hypothesis is needed for this coset-copy construction.

The input arrow `f` is an actual subgroup-equivariant map from
`normalizedAction H X`, the same-space nonempty-chart restriction of `X`,
to the restriction of `Y`. Define the bounded map on coset copy `c` as
`f.hom ≫ Y.ρ c.out`. `extendMap` assembles these arrows by the constructed
disjoint-union descent. `copy_extendMap` recovers precisely this entire
arrow on each copy. The point map sends `(c,x)` to `c.out • f(x)`;
the chosen chart is `(Y.ρ c.out).indexMap (f.hom.indexMap i)` and the
actual bounded pullback is the contravariant composite of the supplied
pullbacks of `f` and `Y.ρ c.out`.

For `g ∈ G`, restricting equivariance to copy `c` first applies the full
original source action at `κ(g,c)`, then the target action at `(g • c).out`.
The complete input equivariance equation moves `f` past the correction.
The representative equation `g * c.out = (g • c).out * κ(g,c)` and the
target action law identify the two composites. Full disjoint-union
extensionality proves `extendMap_equivariant`, and `extendToAction`
packages this actual full-group-equivariant extension.

`unitMap_extendMap` proves the whole-arrow triangle. Express the normalized
unit as the inverse identity-representative action followed by the identity
copy inclusion. Apply `copy_extendMap`, move `f` past that inverse action by
its subgroup equivariance, and cancel the target representative and inverse.
`restrictFromAction` composes the existing normalized unit with subgroup
restriction of an actual equivariant arrow from the induced action.
The triangle proves restriction after extension is the identity.
Conversely, equivariance of an arbitrary arrow and `unitMap_action` recover
its exact restriction on every copy, so full-arrow extensionality proves
extension after restriction is the identity.

`actionExtensionEquiv` packages the resulting bijection
`Hom_G(copiesAction H X, Y) ≃ Hom_H(normalizedAction H X, Res Y)`.
`extendToAction_unique` proves uniqueness from agreement along the full unit.
The correspondence is natural in every original equivariant source arrow
after its nonempty-chart restriction, by unit naturality, and in every
equivariant target arrow, by associativity. Injectivity of the correspondence
and its inverse laws then prove the two corresponding naturality equations
for the constructed extension.

The provenance is internal. The proof route generalizes the existing
`GeneralizedAffinoid.InducedAtlasUniversal` construction from its single
presented-affinoid source to arbitrary supplied overlapping source atlases.
It uses the actual complete disjoint-union descent, original action arrows,
correction identities, constructed natural normalized unit and exact
component recovery. No output extension or universal law is supplied as an
input, and no equality of bounded algebra maps is inferred from points.
The source of the right-hand Hom is the normalized action: empty-chart
deletion generally has no inverse in this chosen-chart category.
Consequently this relative correspondence does not assert an induction
adjunction from the identity on all original presentations. Transport to the
balanced quotient, the explicit nonempty-chart subcategory adjunction,
analytic automorphism continuity, refinement localization, general analytic
sites and the Harris tower specialization remain separate obligations.
