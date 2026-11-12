# Field-valued points on sites of morphisms over an analytic space

Author: Worker 21.

The modules `EtaleGeometricPoints` and `EtaleGeometricPointEquivariance` give,
for an `L`-valued point `x` of an analytic space `X`, a fibre functor on the
étale site `Ét(X)`, a point of the étale site under the point axioms, and the
compatibility of these points with group actions on `X`. This module does the
same for any site `P.Over ⊤ X` of morphisms with a property `P` to `X`, for
any Grothendieck topology `J` on it. It specializes the construction to the
quasi-étale site `Qét(X)` (Library `QuasiEtaleSite`) and checks that the étale
case is the existing one. Worker 26's quasi-étale `G`-sheaves (Task 26) need
these points for compactly supported cohomology.

All declarations are in `Langlands.Analytic.SaturatedAtlasPresentation`. The
field `K` is a complete ultrametric normed field, `L` a normed field with
`[NormedAlgebra K L]`, and spaces lie in `LocalizedCategory.{u, v, v}`.

## Generic construction (`OverSite`)

For `P : MorphismProperty LocalizedCategory` and an `L`-valued point
`x : (localizedFieldPointFunctor L).obj X`:

- `OverSite.pointFibre P L x : P.Over ⊤ X ⥤ Type (max u v uL)` sends
  `U ⟶ X` to the `L`-valued points of `U` lying over `x`. Its definition is
  that of `EtaleSite.pointFibre` with `etale` replaced by `P`.
- `OverSite.PointAxioms P L J x`: the category of elements of the fibre
  functor is cofiltered, and every covering sieve of `J` is jointly surjective
  on fibres.
- `OverSite.toPoint P L J x h : J.Point.{max u (v + 1) uL}`: Mathlib's point of
  the site, with the fibre functor lifted to the universe of the site, as in
  `EtaleSite.toPoint`.
- With `[P.RespectsIso]`:
  - `OverSite.translate P e : P.Over ⊤ X ≌ P.Over ⊤ Y` for `e : X ≅ Y`. It is
    Mathlib's `MorphismProperty.Comma.mapRightIso`, sending `U ⟶ X` to
    `U ⟶ X ⟶ Y`. Its functor for `e = ρ g` is definitionally Task 26's
    `TwistedOver.translate P ρ g`.
  - `OverSite.pointFibreTranslate` and `OverSite.pointTranslate`: the fibre
    of the translate at the image of `x` is the fibre at `x`, by injectivity
    of the bijection of `L`-valued points induced by `e`.
  - `OverSite.pointEquivariance P L ρ J h`: for an action
    `ρ : G →* Aut X` and points satisfying the point axioms, the family
    `x ↦ toPoint P L J x (h x)`, with `G` acting on `L`-valued points by
    `EtaleSite.pointAction`, is a `TwistedOver.PointEquivariance` (Task 26's
    `Langlands.Sheaf.Equivariant.TwistedCompactSupport`).

## The étale site

`EtaleSite.pointFibre_eq`, `EtaleSite.pointAxioms_iff` and
`EtaleSite.translate_eq` (all `rfl` or `Iff.rfl`) identify the published
étale constructions with the generic ones for `P = etale` and
`J = etaleTopology X`.

## The quasi-étale site (`QuasiEtaleSite`)

These are abbreviations of the generic construction for `P = quasiEtale` and
`J = quasiEtaleTopology X`: `QuasiEtaleSite.translate`, `pointFibre`,
`PointAxioms`, `toPoint`, `pointTranslate` and `pointEquivariance`.
`QuasiEtaleSite.translate_functor_eq` records that
`(QuasiEtaleSite.translate (ρ g)).functor` is definitionally
`TwistedOver.translate quasiEtale ρ g`.

## Provenance

The construction follows the published étale modules and SGA 4 IV 6.3 (points
of a site as fibre functors). The geometric meaning, stalks at geometric
points computed by étale neighbourhoods, is Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), registered as
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`, §4.2,
printed p.87 / PDF p.84; see `EtaleGeometricPoints`. The generalization to an
arbitrary morphism property, and the quasi-étale case, are internal. This
module defines and proves no point axioms. Whether geometric points of
complete algebraically closed fields satisfy them is a separate statement
(`EtaleGeometricPointStatement` for the étale site).
