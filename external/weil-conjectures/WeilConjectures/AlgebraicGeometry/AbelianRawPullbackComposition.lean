/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import all WeilConjectures.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift
import all WeilConjectures.AlgebraicGeometry.EtalePullbackSingleComp

/-! # Composition of varying-coefficient raw pullbacks

Source: Stacks Project, Tags 09Z1 and 03CB.
(blueprint: lem-sbc-abelian-raw-pullback-composition).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private lemma singleComp (A : Type (v + 2)) [Category.{v + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{v + 1} A] {X Y Z : Scheme.{v}} (a : Y ⟶ X) (b : Z ⟶ Y)
    (M : Sheaf X.smallEtaleTopology A) :
    (upperStarPlusComp A b a).hom.app ((DerivedCategory.Plus.singleFunctor _ 0).obj M) ≫
      D+((b)^*[A]).map ((((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app M) ≫
      (((b)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app (((a)^*[A]).obj M) =
    (((b ≫ a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app M ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map ((upperStarComp A b a).hom.app M) := by
  rw [upperStarPlusComp, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.plus_single_comp (a)^*[A] (b)^*[A] 0 M]
  exact Functor.plus_single_natIso (upperStarComp A b a) 0 M

private lemma sourceComp (A : Type (v + 2)) [Category.{v + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{v + 1} A] {S X Y Z : Scheme.{v}}
    (h : X ⟶ S) (a : Y ⟶ X) (b : Z ⟶ Y)
    (M : Sheaf S.smallEtaleTopology A) :
    (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp A b (a ≫ h)).hom.app M) ≫
      (((b)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
      D+((b)^*[A]).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map ((upperStarComp A a h).hom.app M) ≫
          (((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _) =
    (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp A (b ≫ a) h (b ≫ a ≫ h) (Category.assoc b a h).symm).hom.app M) ≫
      (((b ≫ a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
      (upperStarPlusComp A b a).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (((h)^*[A]).obj M)) := by
  rw [Functor.map_comp]
  rw [← reassoc_of% ((((b)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.naturality
    ((upperStarComp A a h).hom.app M))]
  rw [← Functor.map_comp_assoc]
  have hc := NatTrans.congr_app (congrArg Iso.hom (upperStarComp_assoc A b a h)) M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hc
  rw [hc, Functor.map_comp]
  simp only [Category.assoc]
  apply (cancel_mono (D+((b)^*[A]).map
    ((((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app (((h)^*[A]).obj M)))).1
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  apply (cancel_mono ((((b)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
    (((a)^*[A]).obj (((h)^*[A]).obj M)))).1
  simp only [Category.assoc]
  rw [singleComp A a b (((h)^*[A]).obj M)]
  simp

private lemma targetComp (A : Type (v + 2)) [Category.{v + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{v + 1} A] {X Y Z : Scheme.{v}}
    (a : Y ⟶ X) (b : Z ⟶ Y) (p : ℤ)
    (F : Sheaf X.smallEtaleTopology A) (F' : Sheaf Y.smallEtaleTopology A)
    (F'' : Sheaf Z.smallEtaleTopology A)
    (φa : ((a)^*[A]).obj F ⟶ F') (φb : ((b)^*[A]).obj F' ⟶ F'') :
    (upperStarPlusComp A b a).hom.app (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦p⟧) ≫
      D+((b)^*[A]).map
        ((D+((a)^*[A]).commShiftIso p).hom.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
          (shiftFunctor _ p).map
            ((((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
              (DerivedCategory.Plus.singleFunctor _ 0).map φa)) ≫
      (D+((b)^*[A]).commShiftIso p).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F') ≫
      (shiftFunctor _ p).map
        ((((b)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F' ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map φb) =
    (D+((b ≫ a)^*[A]).commShiftIso p).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      (shiftFunctor _ p).map
        ((((b ≫ a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarComp A b a).hom.app F ≫ ((b)^*[A]).map φa ≫ φb)) := by
  have : NatTrans.CommShift (upperStarPlusComp A b a).hom ℤ := by
    have := Functor.plusNatIso_commShift (upperStarComp A b a)
    have := Functor.plusCompIso_commShift (a)^*[A] (b)^*[A]
    dsimp only [upperStarPlusComp, Iso.trans_hom]
    infer_instance
  simp only [Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc,
    Functor.commShiftIso_hom_naturality_assoc]
  rw [← reassoc_of% (Functor.commShiftIso_comp_hom_app
    D+((a)^*[A]) D+((b)^*[A]) p ((DerivedCategory.Plus.singleFunctor _ 0).obj F))]
  rw [← NatTrans.shift_app_comm_assoc]
  rw [← Functor.map_comp_assoc]
  rw [← Functor.map_comp_assoc]
  rw [← Functor.map_comp_assoc]
  rw [← Functor.map_comp_assoc]
  congr 1
  simp only [Category.assoc]
  have hn := (((b)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.naturality φa
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  rw [reassoc_of% (singleComp A a b F)]
  simp only [Functor.map_comp, Category.assoc]

private noncomputable def rawGeneral (A : Type (v + 2)) [Category.{v + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{v + 1} A] {S X Y : Scheme.{v}}
    (h : X ⟶ S) (a : Y ⟶ X) (p : ℤ) (M : Sheaf S.smallEtaleTopology A)
    (F : Sheaf X.smallEtaleTopology A) (F' : Sheaf Y.smallEtaleTopology A)
    (φ : ((a)^*[A]).obj F ⟶ F')
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj (((h)^*[A]).obj M) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦p⟧) :=
  (DerivedCategory.Plus.singleFunctor _ 0).map ((upperStarComp A a h).hom.app M) ≫
    (((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
    D+((a)^*[A]).map z ≫
    (D+((a)^*[A]).commShiftIso p).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
    (shiftFunctor _ p).map
      ((((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map φ)

private lemma rawGeneralComp (A : Type (v + 2)) [Category.{v + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{v + 1} A] {S X Y Z : Scheme.{v}}
    (h : X ⟶ S) (a : Y ⟶ X) (b : Z ⟶ Y) (p : ℤ)
    (M : Sheaf S.smallEtaleTopology A)
    (F : Sheaf X.smallEtaleTopology A) (F' : Sheaf Y.smallEtaleTopology A)
    (F'' : Sheaf Z.smallEtaleTopology A)
    (φa : ((a)^*[A]).obj F ⟶ F') (φb : ((b)^*[A]).obj F' ⟶ F'')
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj (((h)^*[A]).obj M) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦p⟧) :
    (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp A (b ≫ a) h (b ≫ a ≫ h) (Category.assoc b a h).symm).hom.app M) ≫
      (((b ≫ a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
      D+((b ≫ a)^*[A]).map z ≫
      (D+((b ≫ a)^*[A]).commShiftIso p).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      (shiftFunctor _ p).map
        ((((b ≫ a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarComp A b a).hom.app F ≫ ((b)^*[A]).map φa ≫ φb)) =
    rawGeneral A (a ≫ h) b p M F' F'' φb (rawGeneral A h a p M F F' φa z) := by
  have hs := sourceComp A h a b M
  have ht := targetComp A a b p F F' F'' φa φb
  simp only [Functor.map_comp, Category.assoc] at hs ht
  dsimp only [rawGeneral]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hs]
  rw [← reassoc_of% ((upperStarPlusComp A b a).hom.naturality z)]
  rw [ht]

/-- Two varying-coefficient raw pullbacks compose on each derived-Hom group.
The composite scheme map and coefficient map may be given with canonical transports.
Source: Stacks Project, Tag 09Z1, canonical comparison maps; Tag 03CB, composition of
inverse images. (blueprint: lem-sbc-abelian-raw-pullback-composition).

Proof: Substitute hd so d is b ≫ a, and convert hφ to equality of morphisms. Expand the
five factors of each raw pullback. Functor.map_comp distributes D(b^*) over the inner
five factors. Naturality of the single-functor comparison for b^* at the source comparison
moves that comparison to the left of the inverse single comparison. The adjacent direct
and inverse single comparisons at the intermediate source then cancel. Use naturality of
the derived composition isomorphism D((b ≫ a)^*) ≅ D(a^*) ⋙ D(b^*) at z to replace the
twice pulled-back class by the class pulled back along b ≫ a. The source factors agree
with the source factor for d by upperStarComp associativity applied to b, a, h. On single
complexes the derived composition agrees with the underived comparison by the proved
exact-functor helpers plus_single_comp and plus_single_natIso in EtalePullbackSingleComp.
The private lemma singleComp combines these identities. Its shift compatibility follows
from the proved plusNatIso_commShift and plusCompIso_commShift helpers in
AbelianDerivedDirectImageTransitionShift. It moves the target component through the two
commShiftIso factors. Naturality of the single comparison at φa moves φa past the intermediate
comparison; functoriality of single and shift combines the coefficient factors as
single(upperStarComp.hom ≫ b^*.map φa ≫ φb). This is single(φd) by hφ. Use wa, wb, wd
and associativity to identify the structure-map equalities (their proof transports are
proof-irrelevant). The five remaining factors are exactly the raw formula for d.
No invertibility of any coefficient morphism is used; zero coefficients, empty schemes,
identity maps and p = 0 obey the same calculation. -/
theorem abelianHigherDirectImageRawPullback_composition {S Y Y' Y'' : Scheme.{v}}
    (a : Y' ⟶ Y) (b : Y'' ⟶ Y') (d : Y'' ⟶ Y) (hd : d = b ≫ a)
    (h : Y ⟶ S) (h' : Y' ⟶ S) (h'' : Y'' ⟶ S)
    (wa : a ≫ h = h') (wb : b ≫ h' = h'') (wd : d ≫ h = h'') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F'' : Sheaf Y''.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φa : ((a)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F')
    (φb : ((b)^*[AddCommGrpCat.{v + 1}]).obj F' ⟶ F'')
    (φd : ((d)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F'')
    (hφ : HEq φd ((upperStarComp AddCommGrpCat.{v + 1} b a).hom.app F ≫
      ((b)^*[AddCommGrpCat.{v + 1}]).map φa ≫ φb))
    (U : S.Etale) (z : (abelianHigherDirectImageRawPresheaf h p F).obj (op U)) :
    abelianHigherDirectImageRawPullback d h h'' wd p F F'' φd U z =
      abelianHigherDirectImageRawPullback b h' h'' wb p F' F'' φb U
        (abelianHigherDirectImageRawPullback a h h' wa p F F' φa U z) := by
  subst d
  subst h'
  subst h''
  have hφ' := eq_of_heq hφ
  subst φd
  exact rawGeneralComp AddCommGrpCat.{v + 1} h a b (p : ℤ) _ F F' F'' φa φb z

end AlgebraicGeometry.Etale
