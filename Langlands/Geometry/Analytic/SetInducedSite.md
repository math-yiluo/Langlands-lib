# Berkovich's functor `γ : Σ ↦ X_Σ(G)` into `Qét(X(G))` and `Ét(X(G))`

Author: Worker 21.

For a `G`-space `X`, this module defines Berkovich's functor `Σ ↦ X_Σ(G)`
from the category `P(G)` of discrete `G`-sets to the quasi-étale category
`Qét(X(G))`, and to the étale category `Ét(X(G))`. Berkovich calls the
resulting morphism of sites `γ`. Here `X_Σ` is the space of module
`SetInducedSpace`: the disjoint union of copies of `X` indexed by `Σ`, with
`g` sending the copy `σ` to the copy `g • σ` by the action of `g` on `X`. Its
structure morphism to `X` is the projection, which is the identity on each
copy.

The module defines the functors. It does not prove that they give morphisms
of sites; that claim is the statement in module `SetInducedSiteStatement`.
Two inputs are not yet proved in the Library, and the functors take them as
hypotheses:

- `hC : ContinuityStatement` (module `SetInducedSpaceContinuityStatement`):
  `X_Σ` is a `G`-space when `X` is a `G`-space and `Σ` has open stabilizers.
  It is needed for `X_Σ(G)` to be an object of `Qét(X(G))` at all.
- `hD : SigmaDescStatement` (module `LocalizedSigmaQuasiEtaleStatement`): a
  morphism out of a disjoint union that is quasi-étale (resp. étale) on every
  piece is quasi-étale (resp. étale). It gives that the projection
  `X_Σ → X` is quasi-étale and étale.

Both are Props, so the functors do not depend on which proofs are supplied.
Everything else in the module is proved. Namespace:
`Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace`.

## Original source

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.2, printed p.4, right after the definition of `X_Σ`:

> The correspondence Σ ↦ X_Σ(G) defines a morphism of sites
> γ : X(G)_qét → P(G) (resp. X(G)_ét → P(G)), and we see that Γ_{X{G}}(F) is
> exactly the G-set that represents the sheaf γ_*F.

A morphism of sites `X(G)_qét → P(G)` goes in the opposite direction to the
functor `P(G) → Qét(X(G))` that defines it. This module constructs that
functor. `P(G)` is the site of module `DiscreteGSetSite`. `Qét(X(G))` and
`Ét(X(G))` are the categories `EquivariantQuasiEtaleSite X` and
`EquivariantEtaleSite X` of the Library.

## Definitions

Let `K` be a complete ultrametric normed field and `G : Type z` a group.

For `X : Action (LocalizedCategory.{u, max z v, max z v}) G` (no topology is
needed):

- `setInducedFunctor X : Action (Type z) G ⥤ Action LocalizedCategory G`:
  `S ↦ setInduced X S.V` on objects. On a morphism of `G`-sets `f` it is
  `map X (Action.gMap f)`. Functoriality is `map_id` and `map_comp` of
  `SetInducedSpace`.
- `overFunctor X : Action (Type z) G ⥤ Over X`: the same with the projection
  `projection X S.V : X_S ⟶ X` as structure morphism (`overFunctor_obj_hom`).
  Morphisms are over `X` by `map_projection`.
- `projectionHom_quasiEtale_etale X hD S`: given `hD`, the projection
  `projectionHom X S : X_S → X` of analytic spaces is quasi-étale and étale.
  By definition it is the morphism out of the disjoint union that is the
  identity on every copy. Identities are quasi-étale and étale, so `hD`
  applies.

Now let `G` be a topological group and `X : GSpace K G` a `G`-space.

- `gSpaceFunctor hC X : DiscreteGSet G ⥤ GSpace K G`: `Σ ↦ X_Σ(G)`, the
  functor `setInducedFunctor X.obj` on discrete `G`-sets, which lands in
  `G`-spaces by `hC` (`gSpaceFunctor_obj_obj`).
- `gSpaceOverFunctor hC X : DiscreteGSet G ⥤ Over X`: the same over `X`, with
  the projection as structure morphism (`gSpaceOverFunctor_obj_hom_hom`).
- `quasiEtaleSiteFunctor hC X hD : DiscreteGSet G ⥤ EquivariantQuasiEtaleSite X`:
  Berkovich's `γ` in the quasi-étale case, `Σ ↦ (X_Σ(G) → X(G))`. The
  structure morphism is quasi-étale by `projectionHom_quasiEtale_etale`.
  `quasiEtaleSiteFunctor_obj_left` and `quasiEtaleSiteFunctor_map_left` say
  that its underlying `G`-spaces and `G`-maps are those of `gSpaceFunctor`.
- `etaleSiteFunctor hC X hD : DiscreteGSet G ⥤ EquivariantEtaleSite X`: `γ` in
  the étale case (`etaleSiteFunctor_obj_left`).
- `etaleSiteFunctor_comp_ofEquivariantEtaleSite`: following the étale version
  by the inclusion `Ét(X(G)) → Qét(X(G))` gives the quasi-étale version. This
  holds by `rfl`.

## Choices

- `γ` is defined on all of `P(G)`, including the empty `G`-set. Its `X_∅` is
  the disjoint union of the empty family.
- On all `G`-sets, `Σ ↦ X_Σ` is defined without any topology; open stabilizers
  are only used, through `hC`, to land in `G`-spaces.
- The universes follow `SetInducedSpace`: `G` and the `G`-sets are in
  `Type z`, and the spaces are in `LocalizedCategory.{u, max z v, max z v}`.
- Berkovich's sheaf `γ_*F`, the functor `Γ_{X{G}}` and the representability
  claim in the quotation are not formalized here; they concern sheaves on
  these sites.
