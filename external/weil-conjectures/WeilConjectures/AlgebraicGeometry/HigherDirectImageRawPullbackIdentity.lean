/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullback
import all WeilConjectures.CategoryTheory.ExtExactFunctorIdentityComparison


public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverNaturality
import all WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyPullbackLaws
import all WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitionIdentity
import all WeilConjectures.CategoryTheory.ExtExactFunctorIdentityComparisonExtension

import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullbackExtension

/-! # Identity of raw cohomology pullback

Source: Stacks Project, Tag 09Z1, canonical cohomology comparison maps.
(blueprint: lem-sbc-higher-image-raw-pullback-identity).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private theorem identity_comparison_commShift
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 C) :
    NatTrans.CommShift (Functor.mapDerivedCategoryNatIso e ≪≫
      Functor.mapDerivedCategoryIdIso C).hom ℤ := by
  let Q := DerivedCategory.Q (C := C)
  let W := HomologicalComplex.quasiIso C (ComplexShape.up ℤ)
  let ε : F.mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      𝟭 (CochainComplex C ℤ) :=
    e.hom.mapHomologicalComplex _ ≫ (Functor.mapHomologicalComplexIdIso C _).hom
  have : NatTrans.CommShift ε ℤ := by
    constructor
    intro m
    ext K i
    simp [ε, Functor.commShiftIso_id_hom_app]
  let τ := (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C).hom
  have hτ : Functor.whiskerLeft Q τ =
      F.mapDerivedCategoryFactors.hom ≫ Functor.whiskerRight ε Q ≫
        Q.leftUnitor.hom ≫ Q.rightUnitor.inv := by
    ext K
    dsimp [τ, ε, Q]
    rw [idFactors, Functor.mapDerivedCategoryNatIso_fac_assoc]
    simp only [Functor.map_comp, Category.comp_id]
  have : NatTrans.CommShift Q.rightUnitor.inv ℤ :=
    NatTrans.CommShift.of_iso_inv Q.rightUnitor ℤ
  have : NatTrans.CommShift (Functor.whiskerLeft Q τ) ℤ := by
    rw [hτ]
    infer_instance
  exact CategoryTheory.Abelian.Ext.commShift_of_localization (W := W) Q τ

set_option backward.isDefEq.respectTransparency false in
private theorem plus_identity_comparison_commShift
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 C) :
    NatTrans.CommShift (Functor.mapDerivedCategoryPlusNatIso e ≪≫
      Functor.mapDerivedCategoryPlusIdIso C).hom ℤ := by
  let τ := (Functor.mapDerivedCategoryPlusNatIso e ≪≫
    Functor.mapDerivedCategoryPlusIdIso C).hom
  have hτ : Functor.whiskerRight τ DerivedCategory.Plus.ι =
      F.mapDerivedCategoryPlusCompatibility.hom ≫
        Functor.whiskerLeft DerivedCategory.Plus.ι
          (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C).hom ≫
        DerivedCategory.Plus.ι.rightUnitor.hom ≫ DerivedCategory.Plus.ι.leftUnitor.inv := by
    apply NatTrans.ext
    funext X
    simp only [τ, Iso.trans_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.map_comp,
      Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusIdIso_hom_app]
    dsimp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom,
      NatTrans.id_app, Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app]
    simp only [Category.id_comp]
    repeat erw [Category.comp_id]
  have : NatTrans.CommShift F.mapDerivedCategoryPlusCompatibility.hom ℤ := by
    change NatTrans.CommShift
      (DerivedCategory.TStructure.t.plus.liftCompιIso
        (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory)
        (fun X ↦ (F.mapDerivedCategoryPlus.obj X).2)).hom ℤ
    infer_instance
  have := identity_comparison_commShift F e
  have : NatTrans.CommShift (DerivedCategory.Plus.ι (C := C)).leftUnitor.inv ℤ :=
    NatTrans.CommShift.of_iso_inv (DerivedCategory.Plus.ι (C := C)).leftUnitor ℤ
  have : NatTrans.CommShift (Functor.whiskerRight τ DerivedCategory.Plus.ι) ℤ := by
    rw [hτ]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight τ DerivedCategory.Plus.ι

set_option backward.isDefEq.respectTransparency false in
private theorem single_identity_transport
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : C ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (e : P ≅ 𝟭 C) (X Y : C) (q : ℤ)
    (z : (DerivedCategory.Plus.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj Y)⟦q⟧) :
    (DerivedCategory.Plus.singleFunctor C 0).map (e.inv.app X) ≫
      (P.mapDerivedCategoryPlusSingleFunctor 0).inv.app X ≫
      P.mapDerivedCategoryPlus.map z ≫
      (P.mapDerivedCategoryPlus.commShiftIso q).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj Y) ≫
      (shiftFunctor _ q).map ((P.mapDerivedCategoryPlusSingleFunctor 0).hom.app Y ≫
        (DerivedCategory.Plus.singleFunctor C 0).map (e.hom.app Y)) = z := by
  let τ := (Functor.mapDerivedCategoryPlusNatIso e ≪≫
    Functor.mapDerivedCategoryPlusIdIso C).hom
  have := plus_identity_comparison_commShift P e
  rw [single_iso_id P e]
  have hs := NatTrans.shift_app_comm τ q ((DerivedCategory.Plus.singleFunctor C 0).obj Y)
  simp only [Functor.commShiftIso_id_hom_app] at hs
  erw [Category.comp_id] at hs
  rw [hs]
  have hn := τ.naturality z
  dsimp only [Functor.id_map] at hn
  rw [hn, ← single_iso_id P e X]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

private theorem single_identity_transport_of_eq
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : C ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (e : P ≅ 𝟭 C) (X Y : C) (q : ℤ)
    (c : X ⟶ P.obj X) (d : P.obj Y ⟶ Y)
    (hc : c = e.inv.app X) (hd : d = e.hom.app Y)
    (z : (DerivedCategory.Plus.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj Y)⟦q⟧) :
    (DerivedCategory.Plus.singleFunctor C 0).map c ≫
      (P.mapDerivedCategoryPlusSingleFunctor 0).inv.app X ≫
      P.mapDerivedCategoryPlus.map z ≫
      (P.mapDerivedCategoryPlus.commShiftIso q).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj Y) ≫
      (shiftFunctor _ q).map ((P.mapDerivedCategoryPlusSingleFunctor 0).hom.app Y ≫
        (DerivedCategory.Plus.singleFunctor C 0).map d) = z := by
  subst c d
  exact single_identity_transport P e X Y q z

private lemma upperStarComp_identity_hom
    {Y S : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] (h : Y ⟶ S)
    (w : h = 𝟙 Y ≫ h)
    (X : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarComp (ModuleCat.{u + 1} Λ) (𝟙 Y) h h w).hom.app X =
      (upperStarId (ModuleCat.{u + 1} Λ) Y).inv.app
        (((h)^*[ModuleCat.{u + 1} Λ]).obj X) := by
  rw [upperStarComp_id_left]
  simp

private lemma upperStarComp_identity_inv
    {Y S : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] (h : Y ⟶ S)
    (w : h = 𝟙 Y ≫ h)
    (X : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarComp (ModuleCat.{u + 1} Λ) (𝟙 Y) h h w).inv.app X =
      (upperStarId (ModuleCat.{u + 1} Λ) Y).hom.app
        (((h)^*[ModuleCat.{u + 1} Λ]).obj X) := by
  rw [upperStarComp_id_left]
  simp

/-- The explicit raw pullback of an identity arrow is the identity on classes.
Source: Stacks Project, Tag 09Z1 (lemma-relative-colimit), canonical comparison maps;
Tag 015F (lemma-right-derived-exact-functor), exact derived inverse image.
(blueprint: lem-sbc-higher-image-raw-pullback-identity).

Proof: Let P be inverse image along the identity scheme map and e:P iso identity
its canonical unit comparison. Apply upperStarComp_id_left separately to A.hom
followed by k and to A.hom. The first factor of raw pullback becomes the single
functor applied to e.inv at the pulled-back free sheaf, and its coefficient factor
becomes the single functor applied to e.hom at A.hom-pullback of G.
Apply e termwise to cochain complexes. Compose its localized transformation with
the exact-derived-functor factorization comparison; fullness of precomposition by
localization gives a natural comparison from D(P) to the identity. Its shift
compatibility follows termwise, descends through localization by faithfulness,
and is preserved on restriction to the fully faithful bounded-below subcategory.
Its component on a single complex is precisely the single-functor comparison
followed by the single of e: in degree zero the component is e, in every other
degree it is the unique map to a zero object. Naturality for the class z and
shift compatibility therefore replace the last four factors in the raw formula
by single(e.hom) followed by z. The first single(e.inv) cancels single(e.hom),
leaving z. This applies in every integer degree, including negative q, and for
zero sheaves, zero classes and empty schemes, without a limit or finiteness
hypothesis. All comparisons are the fixed canonical constructions. -/
theorem higherDirectImageRawOverPullback_id
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A : Over W) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q A).obj (op U)) :
    higherDirectImageRawOverPullback Λ k G q (𝟙 A) U z = z := by
  unfold higherDirectImageRawOverPullback higherDirectImageRawTrianglePullback
    rawTriangleMap
  simp only []
  exact single_identity_transport_of_eq (𝟙 A.left)^*[ModuleCat.{u + 1} Λ]
    (upperStarId (ModuleCat.{u + 1} Λ) A.left)
    (((A.hom ≫ k)^*[ModuleCat.{u + 1} Λ]).obj ((freeSheaf Λ S).obj U))
    (((A.hom)^*[ModuleCat.{u + 1} Λ]).obj G) q _ _
    (upperStarComp_identity_hom Λ (A.hom ≫ k) _ ((freeSheaf Λ S).obj U))
    (upperStarComp_identity_inv Λ A.hom _ G) z

end AlgebraicGeometry.Etale
