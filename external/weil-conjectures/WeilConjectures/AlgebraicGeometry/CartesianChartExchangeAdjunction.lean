/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeCoefficients
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeCore
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeSource
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

private noncomputable def actualAdjunct
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {B T Z X : Scheme.{u}}
    (p : Z ⟶ T) (a : T ⟶ B) (s : Z ⟶ B) (hs : s = p ≫ a)
    (q : Z ⟶ X) (M : Sheaf B.smallEtaleTopology A)
    (F : Sheaf X.smallEtaleTopology A)
    (n : ℕ)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((s)^*[A]).obj M) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((q)^*[A]).obj F))⟦(n : ℤ)⟧) :
    D+((p)^*[A]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((a)^*[A]).obj M)) ⟶
      (D+((q)^*[A]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))⟦(n : ℤ)⟧ :=
  (((p)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app (((a)^*[A]).obj M) ≫
    (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp A p a s hs).inv.app
        M) ≫ z ≫
    (shiftFunctor _ (n : ℤ)).map
      ((((q)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app F)


private lemma comp_single_inv_map
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {X Z Z' : Scheme.{u}}
    (t : Z' ⟶ Z) (q : Z ⟶ X) (q' : Z' ⟶ X) (hq : q' = t ≫ q)
    (F : Sheaf X.smallEtaleTopology A) {C : Type*} [Category C]
    (H : DerivedCategory.Plus (Sheaf Z'.smallEtaleTopology A) ⥤ C) :
    H.map ((((t)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        (((q)^*[A]).obj F)) ≫
      H.map ((DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp A t q q' hq).inv.app F)) ≫
      H.map ((((q')^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app F) =
    H.map (D+((t)^*[A]).map
      ((((q)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app F)) ≫
      H.map ((upperStarCompDerivedPlus A t q q' hq).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg H.map (comp_single_inv A t q q' hq F)

private noncomputable def rawClassPullback
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {B Z Z' : Scheme.{u}}
    (t : Z' ⟶ Z) (h : Z ⟶ B) (h' : Z' ⟶ B) (w : t ≫ h = h')
    (M : Sheaf B.smallEtaleTopology A) (n : ℕ)
    (G : Sheaf Z.smallEtaleTopology A) (G' : Sheaf Z'.smallEtaleTopology A)
    (φ : ((t)^*[A]).obj G ⟶ G')
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj (((h)^*[A]).obj M) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G)⟦(n : ℤ)⟧) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj (((h')^*[A]).obj M) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G')⟦(n : ℤ)⟧ :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp A t h h' w.symm).hom.app M) ≫
    (((t)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app (((h)^*[A]).obj M) ≫
    D+((t)^*[A]).map z ≫
    (D+((t)^*[A]).commShiftIso (n : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G) ≫
    (shiftFunctor _ (n : ℤ)).map
      ((((t)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map φ)

private lemma rawClassPullback_eq_raw {B Z Z' : Scheme.{u}}
    (t : Z' ⟶ Z) (h : Z ⟶ B) (h' : Z' ⟶ B) (w : t ≫ h = h')
    (n : ℕ) (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G' : Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ((t)^*[AddCommGrpCat.{u + 1}]).obj G ⟶ G') (V : B.Etale)
    (z : (abelianHigherDirectImageRawPresheaf h n G).obj (op V)) :
    rawClassPullback AddCommGrpCat.{u + 1} t h h' w
      ((abelianComparisonFree B).obj V) n G G' φ z =
    abelianHigherDirectImageRawPullback t h h' w n G G' φ V z := by
  rfl

private noncomputable def actualTransport
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {B T T' Z Z' X : Scheme.{u}}
    {t : Z' ⟶ Z} {p : Z ⟶ T} {p' : Z' ⟶ T'} {b : T' ⟶ T}
    (θ : D+((b)^*[A]) ⋙ D+((p')^*[A]) ⟶ D+((p)^*[A]) ⋙ D+((t)^*[A]))
    (a : T ⟶ B) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (q : Z ⟶ X) (q' : Z' ⟶ X) (hq : q' = t ≫ q)
    (M : Sheaf B.smallEtaleTopology A) (F : Sheaf X.smallEtaleTopology A) (n : ℕ)
    (z : D+((p)^*[A]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (((a)^*[A]).obj M)) ⟶
      (D+((q)^*[A]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))⟦(n : ℤ)⟧) :=
    D+((p')^*[A]).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarComp A b a a' ha).hom.app
              M) ≫
          (((b)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app
            (((a)^*[A]).obj M)) ≫
      θ.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (((a)^*[A]).obj M)) ≫
      D+((t)^*[A]).map z ≫
      (D+((t)^*[A]).commShiftIso (n : ℤ)).hom.app
        (D+((q)^*[A]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
      (shiftFunctor _ (n : ℤ)).map
        ((upperStarCompDerivedPlus A t q q' hq).inv.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))

-- Expanding chart comparisons and adjunction units needs a local reduction budget.
private lemma actualTransport_eq
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {B T T' Z Z' X : Scheme.{u}}
    {t : Z' ⟶ Z} {p : Z ⟶ T} {p' : Z' ⟶ T'} {b : T' ⟶ T}
    (θ : D+((b)^*[A]) ⋙ D+((p')^*[A]) ⟶ D+((p)^*[A]) ⋙ D+((t)^*[A]))
    (a : T ⟶ B) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (q : Z ⟶ X) (q' : Z' ⟶ X) (hq : q' = t ≫ q)
    (M : Sheaf B.smallEtaleTopology A) (F : Sheaf X.smallEtaleTopology A) (n : ℕ)
    (z : D+((p)^*[A]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (((a)^*[A]).obj M)) ⟶
      (D+((q)^*[A]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))⟦(n : ℤ)⟧) :
    actualTransport A (t := t) (p := p) (p' := p') (b := b) θ a a' ha q q' hq M F n z =
    D+((p')^*[A]).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarComp A b a a' ha).hom.app
              M) ≫
          (((b)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app
            (((a)^*[A]).obj M)) ≫
      θ.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (((a)^*[A]).obj M)) ≫
      D+((t)^*[A]).map z ≫
      (D+((t)^*[A]).commShiftIso (n : ℤ)).hom.app
        (D+((q)^*[A]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
      (shiftFunctor _ (n : ℤ)).map
        ((upperStarCompDerivedPlus A t q q' hq).inv.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  rfl

private lemma actualAdjunct_pullback
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {B T T' Z Z' X : Scheme.{u}}
    (t : Z' ⟶ Z) (p : Z ⟶ T) (p' : Z' ⟶ T') (b : T' ⟶ T)
    (sq : CommSq t p' p b) (a : T ⟶ B) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (s : Z ⟶ B) (hs : s = p ≫ a) (s' : Z' ⟶ B) (hs' : s' = p' ≫ a')
    (q : Z ⟶ X) (q' : Z' ⟶ X) (hq : q' = t ≫ q)
    (M : Sheaf B.smallEtaleTopology A)
    (F : Sheaf X.smallEtaleTopology A) (n : ℕ)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((s)^*[A]).obj M) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((q)^*[A]).obj F))⟦(n : ℤ)⟧) :
    actualAdjunct A p' a' s' hs' q'
      M F n
      (rawClassPullback A t s s'
        (by rw [hs', ha, ← Category.assoc p' b a, ← sq.w, Category.assoc, ← hs]) M n _ _
        ((upperStarComp A t q q' hq).inv.app F) z) =
    D+((p')^*[A]).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarComp A b a a' ha).hom.app
              M) ≫
          (((b)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app
            (((a)^*[A]).obj M)) ≫
      (pullbackSquareComparison A sq).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (((a)^*[A]).obj M)) ≫
      D+((t)^*[A]).map (actualAdjunct A p a s hs q
          M F n z) ≫
      (D+((t)^*[A]).commShiftIso (n : ℤ)).hom.app
        (D+((q)^*[A]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
      (shiftFunctor _ (n : ℤ)).map
        ((upperStarCompDerivedPlus A t q q' hq).inv.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  dsimp only [actualAdjunct, rawClassPullback]
  simp only [Functor.comp_obj, Functor.map_comp, Category.assoc]
  rw [comp_single_inv_map A t q q' hq F
    (shiftFunctor _ (n : ℤ))]
  rw [← reassoc_of% (Functor.commShiftIso_hom_naturality
    D+((t)^*[A])
    ((((q)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app F) (n : ℤ))]
  rw [← reassoc_of% (square_single_source A t p p' b sq a a' ha s hs s' hs' M)]
  simp only [Functor.map_comp, Category.assoc]



-- Expanding chart comparisons and adjunction units needs a local reduction budget.
private lemma actualAdjunct_pullback_block
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {B T T' Z Z' X : Scheme.{u}}
    (t : Z' ⟶ Z) (p : Z ⟶ T) (p' : Z' ⟶ T') (b : T' ⟶ T)
    (sq : CommSq t p' p b) (a : T ⟶ B) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (s : Z ⟶ B) (hs : s = p ≫ a) (s' : Z' ⟶ B) (hs' : s' = p' ≫ a')
    (q : Z ⟶ X) (q' : Z' ⟶ X) (hq : q' = t ≫ q)
    (M : Sheaf B.smallEtaleTopology A)
    (F : Sheaf X.smallEtaleTopology A) (n : ℕ)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((s)^*[A]).obj M) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((q)^*[A]).obj F))⟦(n : ℤ)⟧) :
    actualAdjunct A p' a' s' hs' q'
      M F n
      (rawClassPullback A t s s'
        (by rw [hs', ha, ← Category.assoc p' b a, ← sq.w, Category.assoc, ← hs]) M n _ _
        ((upperStarComp A t q q' hq).inv.app F) z) =
    actualTransport A (t := t) (p := p) (p' := p') (b := b)
      (pullbackSquareComparison A sq).hom a a' ha q q' hq M F n
      (actualAdjunct A p a s hs q M F n z) := by
  rw [actualTransport_eq]
  exact actualAdjunct_pullback A t p p' b sq a a' ha s hs s' hs' q q' hq M F n z

private theorem adjunct_mate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ E) (H : D ⥤ F)
    (θ : TwoSquare G L L' H) {A : C} {K : D} (z : L.obj A ⟶ K) :
    G.map (adj.homEquiv A K z) ≫ (mateEquiv adj adj' θ).app K =
      adj'.homEquiv (G.obj A) (H.obj K) (θ.app A ≫ H.map z) := by
  rw [adj.homEquiv_unit, G.map_comp, Category.assoc]
  have hn := (mateEquiv adj adj' θ).naturality z
  simp only [Functor.comp_map] at hn
  rw [hn]
  rw [← Category.assoc, unit_mateEquiv, Category.assoc, ← R'.map_comp,
    adj'.homEquiv_unit]
  rfl

private theorem shifted_adjunct_mate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    [R.CommShift ℤ] [R'.CommShift ℤ]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ E) (H : D ⥤ F)
    [G.CommShift ℤ] [H.CommShift ℤ] (θ : TwoSquare G L L' H)
    [NatTrans.CommShift (mateEquiv adj adj' θ) ℤ]
    {A : C} {K : D} (q : ℤ) (z : L.obj A ⟶ K⟦q⟧) :
    G.map (adj.homEquiv A (K⟦q⟧) z ≫ (R.commShiftIso q).hom.app K) ≫
        (G.commShiftIso q).hom.app (R.obj K) ≫
        (shiftFunctor E q).map ((mateEquiv adj adj' θ).app K) =
      adj'.homEquiv (G.obj A) ((H.obj K)⟦q⟧)
        (θ.app A ≫ H.map z ≫ (H.commShiftIso q).hom.app K) ≫
          (R'.commShiftIso q).hom.app (H.obj K) := by
  have hs := NatTrans.shift_app_comm (mateEquiv adj adj' θ) q K
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hs
  rw [Functor.map_comp, Category.assoc, hs]
  rw [← Category.assoc, adjunct_mate]
  rw [← Category.assoc, ← adj'.homEquiv_naturality_right, Category.assoc]

private theorem shifted_adjunct_mate_transport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    [R.CommShift ℤ] [R'.CommShift ℤ]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ E) (H : D ⥤ F)
    [G.CommShift ℤ] [H.CommShift ℤ] (θ : TwoSquare G L L' H)
    [NatTrans.CommShift (mateEquiv adj adj' θ) ℤ]
    {A : C} {A' : E} {K : D} {K' : F} (q : ℤ)
    (δ : A' ⟶ G.obj A) (z : L.obj A ⟶ K⟦q⟧) (t : H.obj K ⟶ K') :
    δ ≫ G.map (adj.homEquiv A (K⟦q⟧) z ≫ (R.commShiftIso q).hom.app K) ≫
        (G.commShiftIso q).hom.app (R.obj K) ≫
        (shiftFunctor E q).map
          ((mateEquiv adj adj' θ).app K ≫ R'.map t) =
      adj'.homEquiv A' (K'⟦q⟧)
        (L'.map δ ≫ θ.app A ≫ H.map z ≫
          (H.commShiftIso q).hom.app K ≫ (shiftFunctor F q).map t) ≫
            (R'.commShiftIso q).hom.app K' := by
  have hm := shifted_adjunct_mate adj adj' G H θ q z
  rw [(shiftFunctor E q).map_comp]
  rw [reassoc_of% hm]
  rw [← R'.commShiftIso_hom_naturality]
  rw [← Category.assoc δ _ _, ← adj'.homEquiv_naturality_left]
  rw [← Category.assoc, ← adj'.homEquiv_naturality_right]
  simp only [Category.assoc]

end AlgebraicGeometry.Etale
