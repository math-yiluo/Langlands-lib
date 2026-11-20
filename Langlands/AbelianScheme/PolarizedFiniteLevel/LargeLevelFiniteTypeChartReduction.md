# Finite type of the fine moduli scheme from finite type of the frame charts

The module
`Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelFiniteTypeChartReduction`
proves three auxiliary lemmas and one proved definition. None of them has
hypotheses beyond its displayed arguments. The module sets the Lean option
`backward.isDefEq.respectTransparency.types false`. Without it, instance search
does not find Mathlib's `IsZariskiLocalAtSource` instance for
`LocallyOfFiniteType` or the `HasAffineProperty` instance for `QuasiCompact`
used in the last step.

## Auxiliary lemmas

- `LevelBase.nonempty_iso_ofOpen`. Let `j : Y ⟶ X` be a morphism of level bases
  and `U` an open of `X.obj`. Assume:
  - (injectivity on test points) for every level base `T` and
    `y y' : T ⟶ Y`, `y ≫ j = y' ≫ j` implies `y = y'`;
  - (range) for every level base `T` and `f : T ⟶ X`, `f` factors as `y ≫ j`
    exactly when the set-theoretic range of `f` lies in `U`.

  Then `Y` is isomorphic to the open level base `X.ofOpen U` (module
  `LevelBaseZariski`).

  *Proof.* Applying the range condition to `j` itself shows that the range of `j`
  lies in `U`, so `j` lifts through the open immersion `U.ι`
  (`IsOpenImmersion.lift`). This gives `j' : Y ⟶ X.ofOpen U` with
  `j' ≫ X.openι U = j`. Applying the range condition to `X.openι U` gives
  `s : X.ofOpen U ⟶ Y` with `s ≫ j = X.openι U`. Then `j' ≫ s = 𝟙` by
  injectivity, since both sides composed with `j` give `j`. Also `s ≫ j' = 𝟙`,
  since both sides composed with the monomorphism `U.ι` give `U.ι`.
- `LevelBase.finiteType_of_iso`. If `e : Y ≅ X` is an isomorphism of level bases
  and `Y.toLocalizationSpec` is locally of finite type and quasi-compact, so is
  `X.toLocalizationSpec`. Indeed `X.toLocalizationSpec` equals
  `e.inv.hom ≫ Y.toLocalizationSpec` (`LevelBase.toLocalizationSpec_naturality`).
  This is the composite of an isomorphism of schemes with a morphism having both
  properties.
- `app_eq_hom_app_comp`. Let `α : uliftYoneda.{1}.obj X ≅ F` and
  `a : uliftYoneda.{1}.obj Y ⟶ F` be natural transformations of presheaves on
  level bases. Let `j : Y ⟶ X` be the morphism corresponding to the universal
  point of `a`, namely `j = (α.inv.app (op Y) (a.app (op Y) ⟨𝟙 Y⟩)).down`. Then
  for every `y : T ⟶ Y`, `a.app (op T) ⟨y⟩ = α.hom.app (op T) ⟨y ≫ j⟩`. This is
  the Yoneda lemma, proved from the naturality of `a` and `α.inv` at `y`.

## The reduction

`Langlands.AbelianScheme.PolarizedFiniteLevel.largeLevelFiniteType_of_frameChartFiniteType`
is a proved definition of type

`FrameChartFiniteTypeStatement → FrameLocusBaseChangeStatement.{0} →
FrameLocusCoverStatement.{0} → LargeLevelFiniteTypeStatement`.

It is an internal derivation. It makes no mathematical claim beyond those of its
three premises.

### The proof

Fix `P`, `g`, `d` with `0 < g` and `0 < d`. `FrameChartFiniteTypeStatement`
gives a bound `N₁` and `FrameLocusCoverStatement` gives a bound `N₂`. The bound
is `max N₁ N₂`. Let `n ≥ max N₁ N₂` with `3 ≤ n`, and let `X : LevelBase n`
represent the moduli functor through `α : uliftYoneda.{1}.obj X ≅ moduliFunctor`.

1. *The universal datum.* The moduli functor takes values in a quotient, so the
   class `α.hom.app (op X) ⟨𝟙 X⟩` is `b.classOf` for some datum `b` over `X.obj`.
   By naturality of `α`, for every `f : T ⟶ X` the restriction of `b.classOf`
   along `f` is `α.hom.app (op T) ⟨f⟩`. The components of `α.hom` are injective.
2. *Each frame locus of `b` is of finite type.* Fix `ρ`.
   `FrameChartFiniteTypeStatement` gives a level base `Y`, a natural
   transformation `a` with injective components and the frame-chart property for
   `ρ`, and finite type of `Y.toLocalizationSpec`. Let `j : Y ⟶ X` be the
   morphism of `app_eq_hom_app_comp`. Apply `LevelBase.nonempty_iso_ofOpen` to
   `j` and `U = b.frameLocus ρ`:
   - injectivity on test points follows from `a(y) = α(y ≫ j)` and injectivity
     of the components of `a`;
   - for the range condition, `f : T ⟶ X` factors through `j` exactly when
     `α(f)`, that is the restriction of `b.classOf` along `f`, lies in the image
     of `a.app (op T)`. Here the forward direction uses `a(y) = α(y ≫ j)`, and
     the backward direction uses injectivity of `α`. By the Library lemma
     `frameChart_mem_range_iff` (module `LargeLevelChartCoverReduction`), which
     uses `FrameLocusBaseChangeStatement.{0}`, that holds exactly when the range
     of `f` lies in `b.frameLocus ρ`.

   So `Y ≅ X.ofOpen (b.frameLocus ρ)`, and `LevelBase.finiteType_of_iso` shows
   that the structure morphism of `X.ofOpen (b.frameLocus ρ)` is locally of
   finite type and quasi-compact.
3. *The frame loci cover `X`.* `FrameLocusCoverStatement.{0}`, applied to the
   locally noetherian scheme `X.obj`, on which `n` is a unit, and to the datum
   `b`, puts every point of `X.obj` in some `b.frameLocus ρ`. So the supremum of
   the opens `b.frameLocus ρ` over all `ρ` is `⊤`.
4. *Local finite type.* For each `ρ`, the composite of the open inclusion
   `(b.frameLocus ρ).ι` with `X.toLocalizationSpec` is the structure morphism of
   `X.ofOpen (b.frameLocus ρ)`. This holds because any two morphisms to
   `Spec ℤ[1/n]` agree (`LevelBase.localization_hom_ext`). Local finite type is local on
   the source (`IsZariskiLocalAtSource.of_iSup_eq_top`). So step 2 and step 3
   show that `X.toLocalizationSpec` is locally of finite type.
5. *Quasi-compactness.* Each structure morphism
   `(X.ofOpen (b.frameLocus ρ)).toLocalizationSpec` is quasi-compact with affine
   target, so its source is compact
   (`QuasiCompact.compactSpace_of_compactSpace`). So each `b.frameLocus ρ` is a
   compact subset of `X.obj`. The index type
   `Fin (cubicProjectiveDimension g d + 2) → Fin (2*g) → ZMod n` is finite, since
   `n ≠ 0`. By step 3, `X.obj` is a finite union of compact sets, hence compact.
   A morphism to an affine scheme from a compact scheme is quasi-compact
   (`HasAffineProperty.iff_of_isAffine` for `QuasiCompact`).

## Role

With `largeLevelAmple_of_quasiFiniteProjective` and
`largeLevelQuasiProjectivity_of_ample`, this definition reduces the finite-type
input `LargeLevelFiniteTypeStatement` of the target
`LargeLevelQuasiProjectivityStatement` to three statements:
`FrameChartFiniteTypeStatement`, which is staged with this candidate, and the
published `FrameLocusBaseChangeStatement` and `FrameLocusCoverStatement`.

## Provenance

This is an internal derivation. It combines the conclusions of the three named
statements, documented in their own modules, with standard facts: the Yoneda
lemma, the identification of an open subfunctor with an open subscheme, and the
locality of finite type and quasi-compactness. The argument is the usual proof
that a scheme covered by finitely many open subschemes of finite type over a
base is of finite type over that base.
