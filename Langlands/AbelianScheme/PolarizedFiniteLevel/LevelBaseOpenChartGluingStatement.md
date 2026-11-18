# Representability of a Zariski sheaf on level bases from open charts

`Langlands.AbelianScheme.PolarizedFiniteLevel.LevelBaseOpenChartGluingStatement`
is a proposition definition. It is a statement target only; this module proves
nothing.

## The statement

Let `n : ℕ` and let `F : (LevelBase n)ᵒᵖ ⥤ Type 1` satisfy
`LevelBase.IsZariskiSheaf F`. Let `ι : Type`, let `X : ι → LevelBase n`, and
let `a i : uliftYoneda.{1}.obj (X i) ⟶ F` be natural transformations from the
lifted functors of points. Assume every `a i` is an open chart
(`LevelBase.IsOpenChart`) and that the family covers `F`
(`LevelBase.IsOpenChartCover`). These notions are defined in the internal
module `LevelBaseZariski`. Then there exist:
- a level base `Y`;
- a natural isomorphism `e : uliftYoneda.{1}.obj Y ≅ F`;
- morphisms `j i : X i ⟶ Y` of level bases,

such that every `(j i).hom` is an open immersion of schemes, every point of
`Y` lies in the image of some `j i`, and `uliftYoneda.{1}.map (j i) ≫ e.hom = a i`
for every `i`. So `Y` represents `F`, and the given charts are the open
subschemes `j i` of `Y`.

The extra conclusions about `j i` record what the gluing construction gives.
Downstream they transfer properties of the charts to `Y`, such as
quasi-compactness when `ι` is finite and every `X i` is quasi-compact.

## Provenance

This is an internal adaptation of the Stacks Project, Schemes, Lemma 26.15.4
(tag 01JJ), registered as `stacks-open-chart-representability-2026-11-01`
(file `01JJ.html`). The source considers a contravariant set-valued functor on
all schemes that is a Zariski sheaf, together with a collection of representable
subfunctors that are representable by open immersions and cover the functor.
It concludes that the functor is representable. Its proof glues the
representing schemes `X_i` along the opens `U_ij ⊂ X_i`, where the universal
family of `X_i` lands in the `j`-th subfunctor. The gluing gives a scheme `X`
with an open cover by copies of the `X_i`. The sheaf property then identifies
the functor of points of `X` with `F`.

The present statement differs from the source in three ways:
- The test category is the published full subcategory `LevelBase n` (locally
  noetherian universe-zero schemes on which `n` is a unit) instead of all
  schemes. This category is closed under open subschemes. The glued scheme is
  again locally noetherian with `n` a unit, because it has an open cover by
  such schemes.
- Values lie in `Type 1`, and representability uses `uliftYoneda.{1}`, as in
  the published `moduliFunctor` and `LargeLevelRepresentabilityStatement`.
- The subfunctors are given as images of injective natural transformations
  from functors of points, and the conclusion also records the open charts of
  the representing scheme.

None of these changes affects the gluing argument of the source.
