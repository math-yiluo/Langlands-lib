# Berkovich's spaces `X_Σ` for `G`-sets `Σ`

Author: Worker 21.

For an analytic space `X` with an action of a group `G` and a set `Σ` with an
action of `G`, this module constructs Berkovich's space `X_Σ`. It is the
disjoint union of copies of `X` indexed by `Σ`, and `g ∈ G` sends the copy
indexed by `σ` to the copy indexed by `g • σ` by the action of `g` on `X`.
The module also constructs:

- the functoriality of `X_Σ` in `G`-maps `Σ → Σ'`;
- the projection `X_Σ → X`;
- the isomorphism between `X_{G/N}` for the `G`-set `G ⧸ N` and the induced
  space of 1.1.2 (module `InducedAnalyticSpace`) of the restriction of `X`
  to `N`.

Everything is in Mathlib's categories of actions
`Action (LocalizedCategory.{u, max z v, max z v}) G` on the Library's category
of analytic spaces, and every statement is proved. Namespace:
`Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace`.

## Original source

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.2, printed p.4. There `X` is a `G`-space:

> For a G-set Σ, let X_Σ denote the disjoint union ∐_{σ∈Σ} X_σ (X_σ are
> copies of X) provided with the following action of G: an element g ∈ G
> takes X_σ to X_{gσ} by the action of g on X. (For example, the space
> X_{G/N} associated with the G-set G/N, where N is an open subgroup of G,
> coincides with the space constructed in 1.1.2.) The correspondence
> Σ ↦ X_Σ(G) defines a morphism of sites γ : X(G)_qét → P(G) (resp.
> X(G)_ét → P(G)), and we see that Γ_{X{G}}(F) is exactly the G-set that
> represents the sheaf γ_*F.

Berkovich uses this construction for the morphism of sites `γ` and the functor
`Γ_{X{G}}` above. The same shape occurs in Harris, *Supercuspidal
representations in the cohomology of Drinfel'd upper half spaces* (1997),
registered as `harris-1997-drinfeld-cohomology`, Appendix, (A.1) and (A.6),
printed pp.114–115. There the Rapoport–Zink space is a product of
Drinfeld's space with a set `Δ_v` on which `GL_n(F)` acts. This module does
not formalize that use.

## Construction

Let `K` be a complete ultrametric normed field, `G : Type z` a group,
`X : Action (LocalizedCategory.{u, max z v, max z v}) G` and `S : Type z`
with `[MulAction G S]`. No topology on `G` is involved.

- `copies X S` is the disjoint union of copies of `X.V` indexed by `S`. It is
  the colimit cofan `localizedSigmaCofan` of module `LocalizedDisjointUnion`.
  `isColimitCopies` is its colimit property, `copy X S s` is the inclusion of
  the copy `s`, and `copies_hom_ext` says that a morphism out of the disjoint
  union is determined by its restrictions to the copies.
- `actionMap X S g`: on the copy `s` it is `X.ρ g` followed by the inclusion of
  the copy `g • s` (`copy_actionMap`). This is Berkovich's action.
  `actionMap_one` and `actionMap_mul` (`a(g * k) = a(k) ≫ a(g)`) follow from
  the action axioms on `X` and on `S`.
- `setInduced X S : Action LocalizedCategory G` is the space `X_Σ` for
  `Σ = S` with this action (`setInduced_ρ`).

## Functoriality in the `G`-set

For `G`-sets `S`, `T`, `U` and a `G`-map `f : S →[G] T` (Mathlib's
`MulActionHom`):

- `mapHom X f` sends the copy `s` identically to the copy `f s`
  (`copy_mapHom`);
- `actionMap_mapHom`: it is `G`-equivariant, because `f (g • s) = g • f s`;
- `map X f : setInduced X S ⟶ setInduced X T`, with `map_hom`, `map_id` and
  `map_comp` (`map X (f'.comp f) = map X f ≫ map X f'`).

## The projection to `X`

- `projectionHom X S` is the identity on every copy (`copy_projectionHom`),
  the codiagonal of the disjoint union.
- `actionMap_projectionHom`: it is `G`-equivariant.
- `projection X S : setInduced X S ⟶ X`, with `projection_hom`.
- `map_projection`: `map X f ≫ projection X T = projection X S`.

So `X_Σ` with its projection is a `G`-object over `X`, functorially in `Σ`.
Berkovich's `γ` needs `X_Σ(G)` to be an object of the quasi-étale (or étale)
site of `X(G)`. That needs two more facts, which this module does not
contain: the projection is quasi-étale (étale), and `X_Σ` is a `G`-space
when the stabilizers of `Σ` are open.

## Comparison with the induced space of 1.1.2

Let `N` be a subgroup of `G` and `X_N` the restriction of `X` to `N`
(`(Action.res _ N.subtype).obj X`). The induced space
`InducedSpace.inducedAction N X_N` of 1.1.2 and `setInduced X (G ⧸ N)` have
the same underlying disjoint union of copies of `X.V` indexed by `G ⧸ N`. Their
actions differ. In the induced space, `g` acts from the copy `c` to the copy
`g • c` by the correction `κ(g, c) = (g • c).out⁻¹ * (g * c.out) ∈ N` (Library
`PresentedAffinoidAlgebra.InducedAction.correction`). In `X_{G/N}` it acts
by `g`.

- `inducedIsoHom X N` is `X.ρ c.out` on the copy `c`, and `inducedIsoInv X N`
  is `X.ρ c.out⁻¹` (`copy_inducedIsoHom`, `copy_inducedIsoInv`). They are
  inverse to each other (`inducedIsoHom_inv`, `inducedIsoInv_hom`).
- `inducedActionMap_inducedIsoHom`: `inducedIsoHom` intertwines the two
  actions. On the copy `c` both sides are `X.ρ (g * c.out)` followed by the
  copy `g • c`, by `correction_spec`:
  `g * c.out = (g • c).out * κ(g, c)`.
- `inducedIso X N : InducedSpace.inducedAction N X_N ≅ setInduced X (G ⧸ N)`
  is the resulting isomorphism of `G`-objects (`inducedIso_hom_hom`). This is
  Berkovich's parenthetical remark. Openness of `N` is not needed.
- `inducedIso_hom_projection`: under this isomorphism, the projection
  `X_{G/N} → X` is `InducedSpace.lift N (𝟙 X_N)`. This is the `G`-morphism
  `ϕ′` of 1.1.2 that extends the identity `ϕ = 1` of `X`. On the copy `c` it
  is `X.ρ c.out`, Berkovich's `g_i ϕ f_i^{-1}`.

## Derived choices

- Berkovich takes `X` a `G`-space and `Σ` a discrete `G`-set (an object of
  `P(G)`). The construction does not use the topologies, so here `X` is any
  object of `Action LocalizedCategory G` and `S` any type with a `G`-action.
  The `G`-space property is a separate matter (see above).
- `G`-sets are types with `MulAction` and `G`-maps are `MulActionHom`s.
  Mathlib's category `Action (Type z) G` can be related to them when a functor
  on it is needed.
- Universes: the index type `S : Type z` lies in the universe of `G`, and the
  disjoint union lies in `LocalizedCategory.{u, max z v, max z v}`, as in
  `InducedAnalyticSpace`.

## Scope

Not done here: quasi-étaleness and étaleness of the projection; the `G`-space
property of `X_Σ`; the functor `Σ ↦ X_Σ(G)` into the equivariant quasi-étale
site and the morphism of sites `γ`; Harris's spaces.
