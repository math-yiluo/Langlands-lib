# Berkovich's induced analytic spaces `X_{G/H}`

Author: Worker 21.

For a subgroup `H` of a group `G` and an analytic space `X` with an action of
`H`, this module constructs Berkovich's induced space `X_{G/H}`. It is the
disjoint union of copies of `X` indexed by `G/H`, with an action of `G`, and
it proves the universal property: `G`-morphisms `X_{G/H} → Y` correspond to
`H`-morphisms `X → Y`. Everything is in Mathlib's categories of actions
`Action (LocalizedCategory.{u, max z v, max z v}) G` on the Library's category
of analytic spaces, and all statements are proved. That `X_{G/H}` is a
`G`-space in Berkovich's sense (Hausdorff, continuous action) when `H` is open
and `X` is an `H`-space is a separate statement (module
`InducedSpaceContinuityStatement`). Namespace:
`Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace`.

## Original source

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.1.2 (Construction), printed p.2:

> Let H be an open subgroup of a topological group G, and let X be an
> H-space. Then there is a unique (up to a canonical isomorphism) an
> H-morphism f : X → X′ to a G-space X′ such that any H-morphism ϕ : X → Y to
> a G-space Y extends in a unique way to a G-morphism ϕ′ : X′ → Y. Indeed, let
> G = ∐_{i∈G/H} g_iH with g_0 = 1 (for the coset H), X′ the disjoint union
> ∐_{i∈G/H} X_i, where X_i is a copy of X identified by an isomorphism
> f_i : X ⥲ X_i. An element g ∈ G acts on X′ as follows: if gg_i = g_jh,
> h ∈ H, then g|_{X_i} = f_j h f_i^{-1} : X_i → X_j ⊂ X [sic, for X′]. The morphism
> f = f_0 : X → X′ satisfies the universal property. Indeed, if ϕ : X → Y is a
> H-morphism to a G-space Y, then the required morphism ϕ′ : X′ → Y is defined
> by ϕ′|_{X_i} = g_i ϕ f_i^{-1}. […] The analytic space X′ will be denoted by
> X_{G/H}.

## Construction

Let `K` be a complete ultrametric normed field, `G : Type z` a group, `H` a
subgroup and `X : Action (LocalizedCategory.{u, max z v, max z v}) H`. No
topology and no openness of `H` are needed for the construction and the
universal property.

- `copies H X`: the disjoint union of copies of `X.V` indexed by `G ⧸ H`, as
  the colimit cofan `localizedSigmaCofan` of module `LocalizedDisjointUnion`.
  `isColimitCopies` is its colimit property, `copy H X c` is the inclusion of
  the copy `c`, and `copies_hom_ext` says that morphisms out of the disjoint
  union are determined on the copies.
- Representatives are the chosen `c.out` of Mathlib's quotient, and the
  correction cocycle is the Library's
  `PresentedAffinoidAlgebra.InducedAction.correction`:
  `κ(g, c) = (g • c).out⁻¹ * (g * c.out) ∈ H`, so that
  `g * c.out = (g • c).out * κ(g, c)` (`correction_spec`). This is Berkovich's
  `g g_i = g_j h` with `h = κ(g, c)`.
- `actionMap H X g`: on the copy `c` it is `X.ρ κ(g, c)` followed by the
  inclusion of the copy `g • c` (`copy_actionMap`). This is Berkovich's
  `g|_{X_i} = f_j h f_i^{-1}`.
  - `actionMap_one` follows from `κ(1, c) = 1`.
  - `actionMap_mul`, `a(g * k) = a(k) ≫ a(g)`, follows from the cocycle
    identity `κ(gk, c) = κ(g, k • c) κ(k, c)`.
  - `ρ_comp` converts composition of action morphisms into multiplication.
- `inducedAction H X : Action LocalizedCategory G`: the induced space
  `X_{G/H}` with this action.

## The unit

Mathlib's representative of the coset `H` itself (`baseCoset H`) need not be
`1`, unlike Berkovich's `g_0 = 1`. It is an element `baseRep H` of `H`
(`out_baseCoset_mem`). The unit corrects for this:

- `unitHom H X := X.ρ (baseRep H)⁻¹ ≫ copy H X (baseCoset H)`;
- `unitHom_comm`: it is `H`-equivariant. This uses `smul_baseCoset` and
  `correction_baseCoset`: `κ(h, H) = o⁻¹ h o` for the representative `o`.
- `unit H X : X ⟶ (Action.res _ H.subtype).obj (inducedAction H X)`.

If the representative of `H` is `1`, the unit is Berkovich's `f_0`.

## Universal property

For `Y : Action LocalizedCategory G`:

- `liftHom H f`, for a morphism `f : X.V ⟶ Y.V`: on the copy `c` it is `f`
  followed by `Y.ρ c.out` (`copy_liftHom`). This is Berkovich's
  `ϕ′|_{X_i} = g_i ϕ f_i^{-1}`.
- `actionMap_liftHom`: if `f` is `H`-equivariant, `liftHom H f` is
  `G`-equivariant, by `correction_spec`.
- `unitHom_liftHom`: `unitHom ≫ liftHom H f = f` for `H`-equivariant `f`.
- `liftHom_unitHom_comp`: a `G`-equivariant morphism out of `X_{G/H}` is
  recovered from its composite with the unit. It uses
  `out_smul_baseCoset` and `correction_out_baseCoset`,
  `κ(c.out, H) = baseRep H`.
- `lift H φ`, `unit_comp_lift`, `lift_unit_comp` and `homEquiv H`:
  composition with the unit is a bijection
  `(inducedAction H X ⟶ Y) ≃ (X ⟶ (Action.res _ H.subtype).obj Y)`, with
  inverse `lift`. This is the universal property of 1.1.2, existence and
  uniqueness.

The universal property also holds in the full subcategories of `G`-spaces
(`GSpace`), once `X_{G/H}` is known to be a `G`-space.

## Derived choices

- Berkovich takes `g_0 = 1`; Mathlib's quotient chooses representatives, and
  the unit includes the correction `baseRep H`.
- The universes: the disjoint union indexed by `G ⧸ H : Type z` lies in
  `LocalizedCategory.{u, max z v, max z v}`. So `X` is taken in this category,
  with chart-index universe equal to the space universe as required by the
  saturation equivalence.
- Openness of `H` and the topology of `G` enter only the continuity of the
  action, stated separately.

## Scope

Not done here: the `G`-space property of `X_{G/H}`
(`InducedSpaceContinuityStatement`); functoriality in `X`; the isomorphism
`(X_{H′/H})_{G/H′} ≅ X_{G/H}`; and Example 1.2.1(i) (sites of `X(H)` and
`X_{G/H}(G)`).
