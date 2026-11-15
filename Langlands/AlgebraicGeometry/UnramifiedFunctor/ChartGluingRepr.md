# Murre's Lemma 3: gluing monomorphic étale charts

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingRepr`, last of the five
modules (`ChartGluingFac`, `ChartGluingAdic`, `ChartGluingGerm`, `ChartGluingLocus`,
`ChartGluingRepr`). It proves

```
theorem Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluing.murreChartGluing :
    MurreChartGluingStatement.{u, v}
```

the statement `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartGluingStatement` of the
published module `MurreLocalToGlobalSteps`: Murre's Lemma 3 in the form of SGA 3, XI,
Proposition 3.5 (printed pp. 96–97 of the Gille–Polo recomposition,
`sga3-exposes-xi-xii-xiv-gille-polo-2008`). Let `S` be locally noetherian and
`F : (Over S)ᵒᵖ ⥤ Type v` with `u`-small values satisfying (F1a), (F1b), (F2), (F3); let
`ξᵢ ∈ F(Uᵢ)` (`i : ι : Type u`) be monomorphisms `Uᵢ → F`, infinitesimally étale at every
point, with `Uᵢ → S` locally of finite type, such that every point of `F` with values in a field
factors through some `ξᵢ`. Then `F` is represented by some `q : Y ⟶ S` locally of finite type,
the morphisms `Uᵢ ⟶ Y` corresponding to the `ξᵢ` are open immersions, and they cover `Y`.

## Route

SGA 3 proves 3.5 by showing with 3.1 that the fibre products `Xᵢ ×_F Xⱼ` are open in `Xᵢ` and
gluing the `Xᵢ` along them. The Lean proof applies Mathlib's Zariski local representability
criterion `AlgebraicGeometry.Scheme.LocalRepresentability.representableBy`
(`Mathlib.AlgebraicGeometry.Sites.Representability`), which performs this gluing for a Zariski
sheaf on all schemes with values in `Type u`, given a family of relatively representable open
immersions `yoneda Uᵢ ⟶ F` that is jointly locally surjective. To use it, `F` is shrunk to
`Type u` and replaced by its total presheaf on all schemes.

## Section `TotalSheaf`

For `P : (Over S)ᵒᵖ ⥤ Type u`, `P.overTotal : Schemeᵒᵖ ⥤ Type u` is the total presheaf
`T ↦ Σ (t : T ⟶ S), P(T, t)` of the Library module `Langlands.CategoryTheory.OverTotalPresheaf`,
with `toFibre`/`ofFibre` between `P(T)` and the fibre of `P.overTotal(T.left)` over `T.hom`.

* `total_eq_of_fibre_eq`: elements of the fibre over `T.hom` are determined by `toFibre`.
* `overTotal_isSheafFor_openCover`: if `P` satisfies (F1a), `P.overTotal` is a sheaf for every
  open cover `𝒰` of a scheme `X`. A compatible family `(tᵢ, pᵢ)` first glues the structure
  morphisms `tᵢ` to `t : X ⟶ S` (`glueMorphisms`); the `pᵢ` then form a compatible family for
  `P` on the cover of `Over.mk t`, which glues by (F1a); uniqueness likewise.
* `isSheaf_zariski_of_openCover`: a presheaf on schemes that is a sheaf for every open cover is a
  sheaf for `Scheme.zariskiTopology` (covering sieves contain the sieve of an open cover, and
  pullbacks of open covers are open covers).
* `isSheaf_overTotal`: hence `P.overTotal` is a Zariski sheaf when `P` satisfies (F1a).

These three lemmas are adapted from the private theorems `total_eq_of_fibre_eq`,
`overTotal_isSheafFor_cover` and `isSheaf_zariski_of_openCover` of the Library module
`Langlands.GroupScheme.HomScheme.AdmissibleSheaf` (where the sheaf condition comes from a
different hypothesis); they are restated here because the originals are private.

## Section `Shrink`

`F` has `u`-small values (`SmallValues`), so `FunctorToTypes.shrink.{u} F` (Mathlib,
`Mathlib.CategoryTheory.ShrinkYoneda`) is a presheaf with values in `Type u`, isomorphic to `F`
objectwise through `equivShrink`.

* `shrink_map_equivShrink`: naturality of `equivShrink`.
* `zariskiSheaf_shrink`: (F1a) passes to the shrunk presheaf (`Presieve.isSheafFor_of_nat_equiv`).
* `representableByOfShrink`: a representation of the shrunk presheaf by `Y` gives one of `F`.
* `pt X x`: the element `(X.hom, x)` of the total presheaf of the shrunk presheaf at `X.left`,
  for `x ∈ F(X)`; `pt_fst`, `overTotal_map_pt` (naturality), `pt_injective`, and `eq_pt`
  (every element `b` over `T` is `pt (Over.mk b.1) η` for a unique `η`).

## Section `Charts`

Let `Gtot` be the total presheaf of the shrunk `F`.

* `chart ξ i : yoneda.obj (U i).left ⟶ Gtot`, the morphism corresponding by Yoneda to
  `pt (U i) (ξ i)`; `chart_app` computes it: a morphism `c : T ⟶ Uᵢ` goes to the restriction of
  `pt (U i) (ξ i)` along `c`.
* `chart_app_comp`: if `φ : V ⟶ Uᵢ` (`V` open in `T`) is a factorization of `η|_V` through
  `ξᵢ`, then `chart ξ i` sends `c ≫ φ` to the restriction of `pt (Over.mk t) η` along `c ≫ V.ι`.
* `locus i η : T.left.Opens`, the open set `W (ξ i) η` (open by `ChartGluingLocus.isOpen_W'`).
  `fac_locus`: `η` factors through `ξᵢ` on `locus i η` (`fac_iff_range_subset_W`).
* `isOpenImmersion_presheaf_chart` (SGA 3, XI 3.5 via 3.1): every `chart ξ i` is a relatively
  representable open immersion (`IsOpenImmersion.presheaf`). For `g : yoneda T ⟶ Gtot`,
  corresponding to `η ∈ F(T, t)`, the square with `yoneda (locus i η) ⟶ yoneda Uᵢ` (the
  factorization `φ` of `fac_locus`) and `yoneda (locus i η) ⟶ yoneda T` (the open immersion
  `V.ι`) is a pullback (`MorphismProperty.relative.of_exists`). It is checked objectwise with
  `Types.isPullback_iff`: commutativity is `chart_app_comp`; injectivity holds because `V.ι` is
  a monomorphism; for the existence of the gap map, if `x₂ : T' ⟶ Uᵢ` and `x₃ : T' ⟶ T` have the
  same image in `Gtot`, then `η|_{T'}` factors through `ξᵢ` along `x₃` (`pt_injective`), so `x₃`
  lands in `W (ξ i) η` (`range_subset_W_of_fac`) and lifts to `x : T' ⟶ V`
  (`IsOpenImmersion.lift`); `x ≫ φ = x₂` because `ξᵢ` is a monomorphism.
* `isLocallySurjective_chart`: if every point of `F` with values in a field factors through
  some `ξᵢ`, the map `∐ᵢ yoneda Uᵢ ⟶ Gtot` (`Sigma.desc (chart ξ)`) is locally surjective for
  the Zariski topology. For a section `b = pt (T, t) η`, each point `x` of `T` lies in some
  `locus i η` (apply the hypothesis to the residue field point `resPt`), so these opens form an
  open cover of `T`; on `locus i η`, `b` is the image of the factorization `φ` under the chart
  (`chart_app_comp`).

## Murre's Lemma 3

`murreChartGluing`. Let `Gs` be the Zariski sheaf `Gtot` (`isSheaf_overTotal`,
`zariskiSheaf_shrink`). The charts are relatively representable open immersions and jointly
locally surjective, so `Scheme.LocalRepresentability.representableBy` gives a representation
`eT` of `Gtot` by the glued scheme `Y := (glueData).glued`, in which the chart maps are the
open immersions `toGlued i : Uᵢ ⟶ Y` with `eT.homEquiv (toGlued i) = pt (U i) (ξ i)`
(`yonedaGluedToSheaf_app_toGlued`). Then:

* `q := eT.overTotalBase : Y ⟶ S` and `RepresentableBy.ofOverTotal` (Library,
  `OverTotalPresheaf`) turn `eT` into a representation of the shrunk presheaf by `Over.mk q`;
  `representableByOfShrink` gives `e : F.RepresentableBy (Over.mk q)`. One computes
  `toGlued i ≫ q = (U i).hom` and `(e.homEquiv.symm (ξ i)).left = toGlued i`.
* `q` is locally of finite type: this is local on the source
  (`IsZariskiLocalAtSource.of_openCover` with the instance
  `HasRingHomProperty.instIsZariskiLocalAtSource` supplied explicitly), and on the open cover
  of `Y` by the `Uᵢ` (`glueData.openCover`) the composite `toGlued i ≫ q = (U i).hom` is locally
  of finite type by hypothesis.
* each `(e.homEquiv.symm (ξ i)).left = toGlued i` is an open immersion;
* every point of `Y` is in the image of some `toGlued i` (`GlueData.ι_jointly_surjective`).

## Axioms

`murreChartGluing` depends only on `propext`, `Classical.choice` and `Quot.sound`.
