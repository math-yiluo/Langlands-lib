# Gluing open charts on level bases

This module proves the Library statement
`Langlands.AbelianScheme.PolarizedFiniteLevel.LevelBaseOpenChartGluingStatement`
as the theorem
`Langlands.AbelianScheme.PolarizedFiniteLevel.levelBaseOpenChartGluing`. The
statement holds for every level `n`, every presheaf
`F : (LevelBase n)ᵒᵖ ⥤ Type 1` satisfying `LevelBase.IsZariskiSheaf`, every
index type `ι : Type`, and every family of open charts
`a i : uliftYoneda.{1}.obj (X i) ⟶ F` (`LevelBase.IsOpenChart`) that covers `F`
(`LevelBase.IsOpenChartCover`). The proof adds no hypotheses. Its axioms are
`propext`, `Classical.choice` and `Quot.sound`.

The mathematics is Stacks Project, Schemes, Lemma 26.15.4 (tag 01JJ),
registered as `stacks-open-chart-representability-2026-11-01`. Mathlib's
formalization of that lemma,
`AlgebraicGeometry.Scheme.LocalRepresentability`, needs a `Type u`-valued sheaf
on all of `Scheme.{u}` with Mathlib's relatively representable open immersions.
Here `F` is defined only on the full subcategory `LevelBase n` and takes values
in `Type 1`, so that result does not apply. The proof below glues directly with
`AlgebraicGeometry.Scheme.GlueData`. Its gluing datum follows the pattern of
Mathlib's `Scheme.IsLocallyDirected.glueData`.

## Auxiliary constructions

- `LevelBase.ofOpenImmersion S g` takes an open immersion `g : W ⟶ S.obj` into
  a level base and returns its source `W` as a level base. `W` is locally
  noetherian by `isLocallyNoetherian_of_isOpenImmersion`. `n` is a unit on `W`
  because it is the image of a unit under `g.appTop`. The definition is a
  reducible structure literal, so `(S.ofOpenImmersion g).obj` is syntactically
  `W`. The published `LevelBase.ofOpen` is not reducible, and this keeps
  rewriting steps type-correct.
- `LevelBase.IsZariskiSheaf.ext` is the separation half of the sheaf
  condition: two sections that agree on an open cover are equal.

## The gluing datum (namespace `OpenChartGluing`)

Write `val i g := (a i).app (op W) (ULift.up g)` for `g : W ⟶ X i`, and let
`ξ i := val i (𝟙 (X i))` be the universal point of chart `i`. By naturality
(`val_comp`, `val_eq`), `val i g = F.map g.op (ξ i)`. Injectivity of each
chart gives `val_injective`.

- `Uo i j` is the open of `X i` that `IsOpenChart (a j)` provides for the
  section `ξ i`. A morphism `g : W ⟶ X i` has `val i g` in the image of `a j`
  exactly when the range of `g` lies in `Uo i j` (`mem_range_val_iff`). In
  particular `Uo i i = ⊤` (`Uo_self`).
- Restricting `ξ i` to `Uo i j` lands in the image of `a j`. So there is a
  unique `φ i j : (X i).ofOpen (Uo i j) ⟶ X j` with
  `val j (φ i j) = val i (incl i j)` (`val_φ`). Its range lies in `Uo j i`
  (`range_φ`). Its scheme morphism is `φs i j`, and `t i j : Uo i j ⟶ Uo j i`
  is the lift of `φs i j` through the open immersion `(Uo j i).ι`. The
  identity `val_comp_φ` gives `val j (q ≫ φs i j) = val i (q ≫ ι)` for every
  test level base.
- `t' i j k` maps the triple overlap `Uo i j ×_{X i} Uo i k` to
  `Uo j k ×_{X j} Uo j i`. Its first component is the lift of `fst ≫ φs i j`
  into `Uo j k`. That this map lands in `Uo j k` (`range_fst_φ`) uses the
  pullback as the level base `P i j k` and the stability of chart images
  under restriction (`map_mem_range`). Its second component is `fst ≫ t i j`,
  which gives `t_fac`.
- `t_id` follows from `φ i i = incl i i`, which holds by injectivity. For the
  cocycle condition, `val_t'_π` shows that `t' i j k` carries the base point
  `π i j k` of the triple overlap in `X i` to a base point of `X j` with the
  same value in `F`. Applying this three times shows that the composite
  `t' i j k ≫ t' j k i ≫ t' k i j` has the same value under `a i` as the
  identity. Injectivity of `a i` on the level base `P i j k` then gives
  `cocycle_π`, and `pullback.hom_ext` gives `cocycle`.
- `glueData` is the resulting `Scheme.GlueData`, with `U i = (X i).obj`,
  `V (i, j) = Uo i j` and `f i j = (Uo i j).ι`.

## The glued level base

`Yg` is the glued scheme and `ιg i : (X i).obj ⟶ Yg` are the gluing maps,
which are open immersions. `Yg` is locally noetherian by
`isLocallyNoetherian_iff_openCover` applied to the glued open cover. `n` is a
unit in `Γ(Yg, ⊤)` by `RingedSpace.isUnit_of_isUnit_germ`. At a point `ιg i y`,
the stalk map of `ιg i` is a local ring homomorphism that sends `n` to `n`, and
`n` is a unit in the stalk of `X i` (`isUnit_Yg`). This gives the level base
`Ylb` and the morphisms `jlb i : X i ⟶ Ylb`.

Two comparison lemmas connect the glued scheme with the charts. Here `W` is a
level base, `g : W ⟶ X i` and `h : W ⟶ X j`.

- `comp_ι_eq`: if `val i g = val j h`, then `g ≫ ιg i = h ≫ ιg j`. The range
  of `g` lies in `Uo i j`, so `g` factors as `q ≫ (Uo i j).ι`.
  Injectivity of `a j` gives `q ≫ φs i j = h`, and the gluing condition
  finishes the proof.
- `val_eq_of_comp_eq`: the converse. Lift `(g, h)` through the pullback
  square `vPullbackConeIsLimit` (the overlap of `X i` and `X j` in `Yg` is
  `Uo i j`), then apply `val_comp_φ`.

## The isomorphism with `F`

- On the opens `Vo i`, the ranges of `ιg i`, which cover `Yg` (`iSup_Vo`), the
  sections `s i` are `ξ i` transported along `Vo i ≅ X i` (`ρ i`). They agree
  on overlaps by `val_eq_of_comp_eq` (`s_compat`). The sheaf condition glues
  them to `σ ∈ F(Ylb)` with `F.map (jlb i).op σ = ξ i` (`map_jlb_σ`).
- `e₀ := uliftYonedaEquiv.symm σ`, so `e₀` sends `k : W ⟶ Ylb` to
  `F.map k.op σ`. Hence `e₀ (g ≫ ιg i) = val i g` (`e₀_app_comp`), and
  `uliftYoneda.map (jlb i) ≫ e₀ = a i` (`fac`).
- Injectivity (`e₀_injective`): suppose `F.map g.op σ = F.map h.op σ` for
  `g h : T ⟶ Ylb`. Near each point of `T`, use the open where `g` lands in
  chart `i` and `h` lands in chart `j`. There both maps factor through the
  charts with equal values in `F`, so they agree by `comp_ι_eq`.
  `Scheme.hom_ext_of_forall` concludes `g = h`.
- Surjectivity (`e₀_surjective`): take `ζ ∈ F(T)`. The cover hypothesis gives,
  for each point `x`, a chart `i x` and an open `U x ∋ x` on which `ζ`
  restricts to `val (i x) (g x)` for a unique `g x`. The maps
  `g x ≫ ιg (i x)` agree on the pullbacks `U x ×_T U y`, wrapped as level
  bases, by `comp_ι_eq`. They glue by `Scheme.Cover.glueMorphisms` to
  `G : T ⟶ Yg`. Its value `F.map G.op σ` restricts to the same section as `ζ`
  on every `U x`, so it equals `ζ` by `IsZariskiSheaf.ext`.
- `isIso_e₀`: every component of `e₀` is bijective, so `e₀` is an isomorphism.

## Main theorem

`levelBaseOpenChartGluing` takes `Y := Ylb`, `e := asIso e₀` and `j := jlb`.
Each `(jlb i).hom = ιg i` is an open immersion. The ranges cover `Y` by
`Scheme.GlueData.ι_jointly_surjective`, and the factorization is `fac`.
