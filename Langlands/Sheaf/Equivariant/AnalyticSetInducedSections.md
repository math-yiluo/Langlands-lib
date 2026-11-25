# Berkovich's functor `Γ_{X{G}}` on sheaves on `X(G)_qét` and `X(G)_ét`

Builds on the following modules:

- `Langlands.Topology.GroupAction.DiscreteGSetFibre` (imported; ported together with this module): for a
  presheaf `P` of modules on `P(G)`, the diagram `fibreDiagram P` over the pointed orbits,
  its colimit `fibre P`, the base points `basePoint G`, Berkovich's comparison
  `colimitOpenSubgroupIsoFibre P` with the colimit over the open subgroups, the smooth
  representation `fibreRep P`, the fibre functor `fibreFunctor G R`, and
  `hasColimitsOfShape_pointedOrbit G R`.
- `Langlands.Geometry.Analytic.SetInducedSite` (imported): Berkovich's functor
  `γ : Σ ↦ X_Σ(G)` as `SetInducedSpace.quasiEtaleSiteFunctor hC X hD : P(G) ⥤ Qét(X(G))` and
  `SetInducedSpace.etaleSiteFunctor hC X hD : P(G) ⥤ Ét(X(G))`. Here `X_Σ` is
  `setInduced X.obj Σ`, the disjoint union of copies of `X` indexed by `Σ`, in which `g` maps
  the copy at `σ` to the copy at `g • σ` by the action of `g` on `X`. The two functors take
  the hypotheses `hC : SetInducedSpace.ContinuityStatement` (the action of `G` on `X_Σ` is
  continuous for discrete `Σ`) and `hD : SigmaDescStatement` (morphisms out of a disjoint
  union that are quasi-étale, resp. étale, on every piece are quasi-étale, resp. étale).
  Both are statements in the Library. They are proved by `SetInducedSpace.continuityStatement`
  (`Langlands.Geometry.Analytic.SetInducedSpaceContinuityProof`) and
  `sigmaDesc_quasiEtale_etale` (`Langlands.Geometry.Analytic.LocalizedSigmaQuasiEtaleProof`);
  this module takes them as hypotheses.
- `Langlands.Geometry.Analytic.EquivariantQuasiEtaleSite` and
  `Langlands.Geometry.Analytic.EquivariantEtaleSite` (imported or through the
  imports): `EquivariantQuasiEtaleSite X = Qét(X(G))` and `EquivariantEtaleSite X = Ét(X(G))`,
  their topologies `equivariantQuasiEtaleTopology X` and `equivariantEtaleTopology X`, and
  the functor `EquivariantQuasiEtaleSite.ofEquivariantEtaleSite X : Ét(X(G)) ⥤ Qét(X(G))`.
- Mathlib: `Functor.whiskeringLeft` and `sheafToPresheaf`.

All declarations are in the namespace `Langlands.Sheaf.Equivariant.Analytic`.

## Purpose

Berkovich (1996, §1.2) defines a functor `Γ_{X{G}}` from sheaves on `X(G)_qét` (resp.
`X(G)_ét`) to discrete `G`-sets by `Γ_{X{G}}(F) = lim→_N F(X_{G/N}(G))`, where `N` runs
through the open subgroups of `G`. This module defines `Γ_{X{G}}` on sheaves of `R`-modules,
with values in smooth representations of `G`. It is the composite of three functors, in
this order:

1. forgetting that `F` is a sheaf;
2. restriction along `γ : Σ ↦ X_Σ(G)`, which gives the presheaf `Σ ↦ F(X_Σ(G))` on `P(G)`;
3. the fibre functor of `DiscreteGSetFibre`.

Berkovich's formula `Γ_{X{G}}(F) = lim→_N F(X_{G/N}(G))` holds as an isomorphism of modules.

## Setting

`K : Type u` is a complete ultrametric normed field and `G : Type z` a topological group
(`[IsTopologicalGroup G]`). `X : GSpace.{u, max z v, max z v} K G` is a `G`-space in the
universes of `SetInducedSite`. `R : Type uR` is a commutative ring. Modules live in
`ModuleCat.{max z w} R`, so that colimits over the pointed orbits (a category in `Type z`)
exist (`hasColimitsOfShape_pointedOrbit.{z, w} G R`, provided with `haveI`). Every
declaration takes `hC` and `hD` explicitly, in the order `hC hD X R`.

## Quasi-étale

- `quasiEtaleSetInducedPresheaf hC hD X R`: the functor
  `F ↦ γ.op ⋙ F` from presheaves of `R`-modules on `Qét(X(G))` to presheaves on `P(G)`, with
  `γ = SetInducedSpace.quasiEtaleSiteFunctor hC X hD`. Its value at `Σ` is `F(X_Σ(G))`
  (`quasiEtaleSetInducedPresheaf_obj_obj`, by `rfl`). On a sheaf this is the presheaf
  underlying Berkovich's `γ_*F`.
- `quasiEtaleSetInducedSections hC hD X R`: **Berkovich's `Γ_{X{G}}`**, the functor
  `Sheaf (equivariantQuasiEtaleTopology X) (ModuleCat.{max z w} R) ⥤
  SmoothRep.{uR, z, max z w} R G` given by
  `sheafToPresheaf _ _ ⋙ quasiEtaleSetInducedPresheaf hC hD X R ⋙ fibreFunctor G R`.
  `quasiEtaleSetInducedSections_obj` states, by `rfl`, that its value at `F` is
  `fibreRep` of `Σ ↦ F(X_Σ(G))`. So `Γ_{X{G}}(F)` is the colimit of the `F(X_{G/N}(G))`
  over the pointed orbits `(G ⧸ N, a)`. An element `g ∈ G` sends the image of
  `F(X_{G/N}(G))` at `a` to its image at `g • a`. The representation is smooth by
  `isSmooth_fibreRepresentation`.
- `quasiEtaleSetInducedSectionsIso hC hD X R F`: **Berkovich's formula**. It is an
  isomorphism of modules from the colimit, over the open subgroups `N` ordered by reverse
  inclusion, of `F(X_{G/N}(G))` with the restrictions along the projections
  `X_{G/N}(G) → X_{G/N'}(G)` for `N ≤ N'`, to the module of `Γ_{X{G}}(F)`. It is
  `colimitOpenSubgroupIsoFibre`.

## Étale

`etaleSetInducedPresheaf`, `etaleSetInducedPresheaf_obj_obj`, `etaleSetInducedSections`,
`etaleSetInducedSections_obj` and `etaleSetInducedSectionsIso` are the same constructions
for `Ét(X(G))`, with `SetInducedSpace.etaleSiteFunctor hC X hD` and
`equivariantEtaleTopology X`.

`etaleSetInducedPresheaf_comp` states, by `rfl`, that for a presheaf `F` on `Qét(X(G))` the
étale presheaf `Σ ↦ F(X_Σ(G))` of the restriction of `F` to `Ét(X(G))` is the quasi-étale one.
This rests on the Library's `etaleSiteFunctor_comp_ofEquivariantEtaleSite`.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).
Printed page numbers equal PDF page numbers. §1.2, printed p.4:

> We also denote by Γ_{X{G}} the functor from X(G)~_qét (resp. X(G)~_ét) to the category of
> (discrete) G-sets by Γ_{X{G}}(F) = lim→_N F(X_{G/N}(G)), where N runs through open
> subgroups of G.

Printed pp.4–5:

> The correspondence Σ ↦ X_Σ(G) defines a morphism of sites γ : X(G)_qét → P(G) (resp.
> X(G)_ét → P(G)), and we see that Γ_{X{G}}(F) is exactly the G-set that represents the
> sheaf γ_*F. It follows also that for any open subgroup N ⊂ G one has
> Γ_{X{G}}(F)^N = F(X_{G/N}(G)).

## Provenance

Derived. Berkovich defines `Γ_{X{G}}` for sheaves of sets, with values in discrete `G`-sets,
and gets the action of `G` from the representability of `γ_*F`. Here `F` is a sheaf of
`R`-modules, and the action comes from the fibre of `γ_*F` over the pointed orbits (see the
Provenance section of `DiscreteGSetFibre`). That `g` sends the image at `a` to the image at
`g • a` is the action of `G` on the `G`-set representing `γ_*F`. This identification is an
informal remark; it is not formalized. Berkovich's formula `lim→_N` is proved as
`quasiEtaleSetInducedSectionsIso` and `etaleSetInducedSectionsIso`. The presheaf
`Σ ↦ F(X_Σ(G))` is the presheaf underlying `γ_*F`, but no sheaf `γ_*F` on `P(G)` is
constructed, and the continuity of `γ` is not used.

The hypotheses `hC` and `hD` are inherited from `SetInducedSite`. The construction uses no
other geometric input.

## Not claimed

- That `γ` is a morphism of sites, that `γ_*F` is a sheaf on `P(G)`, or that `Γ_{X{G}}(F)`
  represents it.
- `Γ_{X{G}}(F)^N = F(X_{G/N}(G))`.
- The derived functors `H^q(X{G}, F)` and the spectral sequence
  `H^p(G, H^q(X{G}, F)) ⇒ H^{p+q}(X(G), F)`.
- Any comparison with the invariant sections `Γ_{X(G)}` of `AnalyticInvariantPresheaf`.
