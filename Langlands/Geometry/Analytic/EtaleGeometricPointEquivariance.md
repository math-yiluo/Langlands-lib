# Group actions on the field-valued points of an analytic space

Author: Worker 21.

A group `G` acting on an analytic space `X` by automorphisms
(`ρ : G →* Aut X` in the localized category) permutes the `L`-valued points of
`X` (module `FieldValuedPoints`). This module records the action and the
compatibility of the points of `Ét(X)` (module `EtaleGeometricPoints`) with
the translations `U ↦ gU` (module `EtaleSite`). It packages them in the
published `Langlands.Sheaf.Equivariant.TwistedOver.PointEquivariance` of
module `Langlands.Sheaf.Equivariant.TwistedCompactSupport` (Worker 26), which
is used there for compactly supported sections.

## Original source and derived provenance

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`), §1.4,
printed p.7: "F is a G-sheaf if for each quasi-étale (resp. étale) morphism
U → X and for each g ∈ G there is a functorial bijection F(U) ⥲ F(^gU) :
f ↦ ^gf, where ^gU = U ×_{X,g⁻¹} X, such that ^{gh}f = ^g(^hf)." Here `^gU`
carries a left superscript `g` in the original. As explained in `EtaleSite`,
the Library's `translate (ρ g)` sends `U → X` to the composite with `ρ g`,
which is isomorphic over `X` to `^gU`.

The action on `L`-valued points, the identification of the fibres of `^gU`
over `g • x` with those of `U` over `x`, and their packaging are derived.

## Declarations

In `Langlands.Analytic.SaturatedAtlasPresentation.EtaleSite`, for
`X : LocalizedCategory.{u, v, v}`, a group `G` and `ρ : G →* Aut X`, writing
`P = localizedFieldPointFunctor L`:

- `pointAction L ρ : MulAction G (P.obj X)`, with `g • x = P.map (ρ g).hom x`
  (`pointAction_smul`). The unit and multiplication laws follow from
  `map_one`, `map_mul` of `ρ`, the composition order of `Aut X`, and the
  functor laws of `P`. It is an `abbrev`, not a global instance, since it
  depends on `ρ`.
- `pointEquivariance L ρ h`, for `h : ∀ x : P.obj X, PointAxioms L x`: with the
  action `pointAction L ρ`, a `TwistedOver.PointEquivariance` for the
  morphism property `etale`, the topology `etaleTopology X` and the family of
  points `fun x => toPoint L x (h x)`. Its field `fiberIso g x` is
  `pointTranslate L (ρ g) x (h x) (h (g • x))`. Worker 26's `translate etale ρ g`
  is definitionally `(translate (ρ g)).functor`.

## Scope

Not proved here: the hypothesis `h` (asserted for algebraically closed
complete `L` in `EtaleGeometricPointStatement`), and any topology on the set
of `L`-valued points.
