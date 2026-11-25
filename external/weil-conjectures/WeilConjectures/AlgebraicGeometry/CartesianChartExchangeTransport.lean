/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeCoefficients
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeCore
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeAdjunction
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc
-- Internal comparison lemmas are shared through private imports.
set_option linter.privateModule false

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency true
set_option linter.unusedSimpArgs false
set_option linter.privateModule false

private lemma add_iso_trans_apply {A B C : AddCommGrpCat.{u}}
    (e : A ≅ B) (f : B ≅ C) (z : A) : (e ≪≫ f).hom z = f.hom (e.hom z) := by
  rfl

private lemma yoneda_mapIso_apply
    {C : Type*} [Category C] [Preadditive C] {A A' B : C}
    (e : A ≅ A') (z : A' ⟶ B) :
    ((preadditiveYoneda.obj B).mapIso e.op).hom z = e.hom ≫ z := by
  rfl

private lemma coyoneda_mapIso_apply
    {C : Type*} [Category C] [Preadditive C] {A B B' : C}
    (e : B ≅ B') (z : A ⟶ B) :
    ((preadditiveCoyoneda.obj (op A)).mapIso e).hom z = z ≫ e.hom := by
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma chartAdjunct_as_actual {S X B T : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S) (w : g' = a ≫ g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (V : B.Etale)
    (z : (abelianHigherDirectImageRawPresheaf
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) n
      (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V)) :
    (cartesianChartAdjunctIso f g a g' w F n V).hom z =
      actualAdjunct AddCommGrpCat.{u + 1} (pullback.snd f g') a (pullback.snd f g' ≫ a) rfl
        (pullback.fst f g') ((abelianComparisonFree B).obj V) F n
        (abelianHigherDirectImageRawPullback (cartesianChartSourceIso f g a g' w).inv
          (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g)
          (pullback.snd f g' ≫ a)
          (by rw [← pullback.condition, ← Category.assoc, cartesianChartSourceIso_inv_fst])
          n _ _ (cartesianChartCoefficientIso f g a g' w F).hom V z) := by
  dsimp only [cartesianChartAdjunctIso]
  rw [add_iso_trans_apply, add_iso_trans_apply]
  erw [coyoneda_mapIso_apply, yoneda_mapIso_apply, abelianRawIsoPullback_hom]
  simp only [actualAdjunct, Iso.symm_hom, Iso.symm_inv, Iso.trans_inv, Functor.mapIso_inv,
    Functor.mapIso_hom, Iso.app_inv, Iso.app_hom, Category.assoc]

private lemma chartCoefficient_hom {S X B T : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S) (w : g' = a ≫ g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (cartesianChartCoefficientIso f g a g' w F).hom =
      flatten (cartesianChartSourceIso f g a g' w).inv
        (pullback.snd a (pullback.snd f g)) (pullback.fst f g)
        ((cartesianChartSourceIso f g a g' w).inv ≫ pullback.snd a (pullback.snd f g))
        (pullback.fst f g') rfl
        (cartesianChartSourceIso_inv_snd_fst f g a g' w).symm F := by
  rfl

private lemma chart_inv_diagonal {S X B T : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S) (w : g' = a ≫ g) :
    (cartesianChartSourceIso f g a g' w).inv ≫
      pullback.snd a (pullback.snd f g) ≫ pullback.snd f g = pullback.snd f g' ≫ a := by
  rw [← pullback.condition, ← Category.assoc, cartesianChartSourceIso_inv_fst]

private lemma chart_inv_leg {S X B T T' : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S) (w : g' = a ≫ g)
    (b : T' ⟶ T) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (g'' : T' ⟶ S) (w' : g'' = a' ≫ g) (wb : g'' = b ≫ g')
    (l : pullback a' (pullback.snd f g) ⟶ pullback a (pullback.snd f g))
    (hl₁ : l ≫ pullback.fst a (pullback.snd f g) =
      pullback.fst a' (pullback.snd f g) ≫ b)
    (hl₂ : l ≫ pullback.snd a (pullback.snd f g) = pullback.snd a' (pullback.snd f g)) :
    (cartesianChartSourceIso f g a' g'' w').inv ≫ l =
      cartesianImageProjection f g' g'' b wb ≫ (cartesianChartSourceIso f g a g' w).inv := by
  apply pullback.hom_ext
  · calc
      ((cartesianChartSourceIso f g a' g'' w').inv ≫ l) ≫
          pullback.fst a (pullback.snd f g) =
        (cartesianChartSourceIso f g a' g'' w').inv ≫
          (pullback.fst a' (pullback.snd f g) ≫ b) := by rw [Category.assoc, hl₁]
      _ = pullback.snd f g'' ≫ b := by
        rw [← Category.assoc, cartesianChartSourceIso_inv_fst]
      _ = (cartesianImageProjection f g' g'' b wb ≫
          (cartesianChartSourceIso f g a g' w).inv) ≫
            pullback.fst a (pullback.snd f g) := by
        simp only [Category.assoc, cartesianChartSourceIso_inv_fst, cartesianImageProjection_snd]
  · rw [Category.assoc, hl₂, Category.assoc]
    apply pullback.hom_ext
    · simp only [Category.assoc, cartesianChartSourceIso_inv_snd_fst,
        cartesianImageProjection_fst]
    · simp only [Category.assoc, chart_inv_diagonal]
      rw [← Category.assoc, cartesianImageProjection_snd]
      simp only [ha, Category.assoc]

-- Expanding chart comparisons and adjunction units needs a local reduction budget.
private lemma chartAdjunct_pullback {S X B T T' : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S) (w : g' = a ≫ g)
    (b : T' ⟶ T) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (g'' : T' ⟶ S) (w' : g'' = a' ≫ g) (wb : g'' = b ≫ g')
    (l : pullback a' (pullback.snd f g) ⟶ pullback a (pullback.snd f g))
    (hl₁ : l ≫ pullback.fst a (pullback.snd f g) =
      pullback.fst a' (pullback.snd f g) ≫ b)
    (hl₂ : l ≫ pullback.snd a (pullback.snd f g) = pullback.snd a' (pullback.snd f g))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (V : B.Etale)
    (z : (abelianHigherDirectImageRawPresheaf
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) n
      (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V)) :
    let t := cartesianImageProjection f g' g'' b wb
    let sq : CommSq t (pullback.snd f g'') (pullback.snd f g') b := ⟨by simp [t]⟩
    (cartesianChartAdjunctIso f g a' g'' w' F n V).hom
      (abelianHigherDirectImageRawPullback l
        (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g)
        (pullback.snd a' (pullback.snd f g) ≫ pullback.snd f g)
        (by rw [← Category.assoc, hl₂]) n _ _
        ((upperStarComp AddCommGrpCat.{u + 1} l
          (pullback.snd a (pullback.snd f g)) (pullback.snd a' (pullback.snd f g))
          hl₂.symm).inv.app (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F)) V z) =
      actualTransport AddCommGrpCat.{u + 1}
        (pullbackSquareComparison AddCommGrpCat.{u + 1} sq).hom a a' ha
        (pullback.fst f g') (pullback.fst f g'')
        (cartesianImageProjection_fst f g' g'' b wb).symm
        ((abelianComparisonFree B).obj V) F n
        ((cartesianChartAdjunctIso f g a g' w F n V).hom z) := by
  dsimp only
  let e := (cartesianChartSourceIso f g a g' w).inv
  let e' := (cartesianChartSourceIso f g a' g'' w').inv
  let v := pullback.snd a (pullback.snd f g)
  let v' := pullback.snd a' (pullback.snd f g)
  let t := cartesianImageProjection f g' g'' b wb
  let d := e' ≫ l
  let dv := e' ≫ v'
  have hdt : d = t ≫ e := chart_inv_leg f g a g' w b a' ha g'' w' wb l hl₁ hl₂
  have hdv : dv = d ≫ v := by
    dsimp only [dv, d, v, v', e']
    rw [Category.assoc, hl₂]
  have hs : pullback.snd f g' ≫ a = e ≫ (v ≫ pullback.snd f g) :=
    (chart_inv_diagonal f g a g' w).symm
  have hs' : pullback.snd f g'' ≫ a' = d ≫ (v ≫ pullback.snd f g) := by
    rw [← chart_inv_diagonal f g a' g'' w']
    dsimp only [d, v, e', v']
    simp only [Category.assoc]
    rw [reassoc_of% hl₂]
  have hq : pullback.fst f g' = (e ≫ v) ≫ pullback.fst f g :=
    (cartesianChartSourceIso_inv_snd_fst f g a g' w).symm
  have hq' : pullback.fst f g'' = dv ≫ pullback.fst f g :=
    (cartesianChartSourceIso_inv_snd_fst f g a' g'' w').symm
  have hraw := raw_coefficient_square l e e' t d rfl hdt v v' hl₂.symm
    (e ≫ v) rfl dv hdv (pullback.snd f g) _ rfl _ rfl
    (pullback.snd f g' ≫ a) hs (pullback.snd f g'' ≫ a') hs'
    (pullback.fst f g) (pullback.fst f g') hq (pullback.fst f g'') hq' F n V z
  dsimp only [d, dv, e, e', v, v', t] at hraw
  rw [chartAdjunct_as_actual, chartAdjunct_as_actual]
  rw [chartCoefficient_hom, chartCoefficient_hom]
  conv_lhs =>
    arg -1
    rw [hraw]
  conv_lhs =>
    arg -1
    rw [← rawClassPullback_eq_raw]
  have hfinal := actualAdjunct_pullback_block AddCommGrpCat.{u + 1} t (pullback.snd f g')
    (pullback.snd f g'') b
    ⟨cartesianImageProjection_snd f g' g'' b wb⟩ a a' ha _ rfl _ rfl
    (pullback.fst f g') (pullback.fst f g'')
    (cartesianImageProjection_fst f g' g'' b wb).symm
    ((abelianComparisonFree B).obj V) F n
    (abelianHigherDirectImageRawPullback e (v ≫ pullback.snd f g)
      (pullback.snd f g' ≫ a) hs.symm n _ _
      (flatten e v (pullback.fst f g) (e ≫ v) (pullback.fst f g') rfl hq F) V z)
  exact hfinal

end AlgebraicGeometry.Etale
