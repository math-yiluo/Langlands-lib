/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import all WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageCoreComp

/-! # Identity of varying-coefficient raw pullback

Source: Stacks Project, Tags 09Z1 and 03CB.
(blueprint: lem-sbc-abelian-raw-pullback-identity).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false in
private lemma id_single {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (X : C) :
    (mapDerivedCategoryPlusIdIso C).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X) =
      ((𝟭 C).mapDerivedCategoryPlusSingleFunctor 0).hom.app X := by
  apply DerivedCategory.Plus.ι.map_injective
  rw [ι_map_mapDerivedCategoryPlusIdIso_hom_app,
    ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app]
  exact mapDerivedCategoryIdIso_hom_app_singleFunctor_obj X

set_option backward.isDefEq.respectTransparency false in
private lemma identity_commShift {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {P : C ⥤ C} [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] (e₀ : P ≅ 𝟭 C) :
    NatTrans.CommShift (mapDerivedCategoryPlusNatIso e₀ ≪≫
      mapDerivedCategoryPlusIdIso C).hom ℤ := by
  let e := mapDerivedCategoryPlusNatIso e₀ ≪≫ mapDerivedCategoryPlusIdIso C
  have hf : Functor.whiskerLeft DerivedCategory.Plus.Qh e.hom =
      P.mapDerivedCategoryPlusFactorsh.hom ≫
        Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus e₀.hom)
          DerivedCategory.Plus.Qh ≫
        Functor.whiskerRight (Functor.mapHomotopyCategoryPlusIdIso C).hom
          DerivedCategory.Plus.Qh ≫
        DerivedCategory.Plus.Qh.leftUnitor.hom ≫
        DerivedCategory.Plus.Qh.rightUnitor.inv := by
    apply NatTrans.ext
    funext K
    dsimp only [e]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Functor.mapHomotopyCategoryPlusIdIso_hom_app_eq_id]
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
    dsimp only [Iso.trans_hom, NatTrans.comp_app]
    rw [mapDerivedCategoryPlusIdIso_hom_app_factorsh,
      mapDerivedCategoryPlusNatIso_hom_app_factorsh]
    erw [Category.comp_id]
  have hidC : NatTrans.CommShift
      (Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom ℤ := by
    constructor
    intro n
    ext K i
    simp [Functor.commShiftIso_id_hom_app]
  have hidH : NatTrans.CommShift
      (Functor.mapHomotopyCategoryIdIso C (.up ℤ)).hom ℤ := by
    let q := HomotopyCategory.quotient C (.up ℤ)
    have hf : Functor.whiskerLeft q (Functor.mapHomotopyCategoryIdIso C (.up ℤ)).hom =
        ((𝟭 C).mapHomotopyCategoryFactors (.up ℤ)).hom ≫
          Functor.whiskerRight (Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom q ≫
            q.leftUnitor.hom ≫ q.rightUnitor.inv := by
      apply NatTrans.ext
      funext K
      dsimp only [q]
      simp only [Functor.whiskerLeft_app, NatTrans.comp_app]
      rw [Functor.mapHomotopyCategoryIdIso_hom_app]
      simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom,
        Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
        Functor.rightUnitor_inv_app, Category.comp_id]
      erw [Category.id_comp, Category.comp_id]
    have : NatTrans.CommShift
        (Functor.whiskerLeft q (Functor.mapHomotopyCategoryIdIso C (.up ℤ)).hom) ℤ := by
      rw [hf]
      infer_instance
    apply NatTrans.CommShift.of_whiskerLeft _ q
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    exact ⟨K, 𝟙 _, inferInstance⟩
  have hid : NatTrans.CommShift (Functor.mapHomotopyCategoryPlusIdIso C).hom ℤ := by
    let j := HomotopyCategory.Plus.ι C
    have hf : Functor.whiskerRight (Functor.mapHomotopyCategoryPlusIdIso C).hom j =
        ((HomotopyCategory.plus C).liftCompιIso
          (j ⋙ (𝟭 C).mapHomotopyCategory (.up ℤ)) _).hom ≫
        Functor.whiskerLeft j (Functor.mapHomotopyCategoryIdIso C (.up ℤ)).hom ≫
          j.rightUnitor.hom ≫ j.leftUnitor.inv := by
      apply NatTrans.ext
      funext K
      simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
        ObjectProperty.liftCompιIso, Iso.refl_hom, Category.id_comp, Category.comp_id]
      erw [Category.comp_id]
      exact Functor.ι_map_mapHomotopyCategoryPlusIdIso_hom_app C K
    have : NatTrans.CommShift
        (Functor.whiskerRight (Functor.mapHomotopyCategoryPlusIdIso C).hom j) ℤ := by
      rw [hf]
      infer_instance
    exact NatTrans.CommShift.of_whiskerRight _ j
  have : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Plus.Qh e.hom) ℤ := by
    rw [hf]
    infer_instance
  apply NatTrans.CommShift.of_whiskerLeft e.hom DerivedCategory.Plus.Qh
  intro X
  exact ⟨DerivedCategory.Plus.Qh.objPreimage X,
    (DerivedCategory.Plus.Qh.objObjPreimageIso X).inv, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
private lemma identity_single_shift {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {P : C ⥤ C} [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (e₀ : P ≅ 𝟭 C) (X F : C) (n : ℤ)
    (z : (DerivedCategory.Plus.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj F)⟦n⟧) :
    (DerivedCategory.Plus.singleFunctor C 0).map (e₀.inv.app X) ≫
      (P.mapDerivedCategoryPlusSingleFunctor 0).inv.app X ≫
      P.mapDerivedCategoryPlus.map z ≫
      (P.mapDerivedCategoryPlus.commShiftIso n).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj F) ≫
      (shiftFunctor _ n).map
        ((P.mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
          (DerivedCategory.Plus.singleFunctor C 0).map (e₀.hom.app F)) = z := by
  let e := mapDerivedCategoryPlusNatIso e₀ ≪≫ mapDerivedCategoryPlusIdIso C
  have hs (A : C) : e.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj A) =
      (P.mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫
        (DerivedCategory.Plus.singleFunctor C 0).map (e₀.hom.app A) := by
    dsimp only [e, Iso.trans_hom, NatTrans.comp_app]
    rw [id_single]
    exact AlgebraicGeometry.Etale.plus_single_natIso e₀ 0 A
  have hc : NatTrans.CommShift e.hom ℤ := identity_commShift e₀
  rw [← hs F]
  erw [NatTrans.shift_app_comm]
  simp only [Functor.commShiftIso_id_hom_app]
  erw [Category.comp_id, e.hom.naturality z]
  dsimp only [Functor.id_map]
  rw [hs]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- Raw pullback along an identity scheme map, with its canonical coefficient map,
is the identity on each derived-Hom group. The equality `ha` permits functor-map transports.
Source: Stacks Project, Tag 09Z1, canonical comparison maps; Tag 03CB, identity of inverse
images. (blueprint: lem-sbc-abelian-raw-pullback-identity).

Proof: Substitute ha, so a is the identity, and convert hφ to equality of morphisms.
The left unit law upperStarComp_id_left identifies the first raw factor with the single
functor applied to upperStarId.inv at h-pullback of the free sheaf of U. Let eD be the
canonical derived identity comparison upperStarIdDerivedPlus. On a single complex its
component is the single-functor comparison followed by single(upperStarId.hom): compute
on the complex concentrated in degree zero, where both maps are upperStarId.hom; in all
other degrees they are the unique map between zero objects. Apply the factorization
comparison and localization to obtain this equality in the derived category, then restrict
to D⁺ using the fully faithful inclusion. The same termwise computation shows that eD
commutes with shifts. Consequently the last three factors of the raw formula are
D(id^*).map z followed by eD.hom at the shifted single of F. Naturality of eD changes
this to eD.hom at the source single followed by z. The inverse single comparison cancels
its direct comparison. What remains is single(upperStarId.inv) followed by
single(upperStarId.hom) followed by z; functoriality and the inverse-hom identity give z.
This proof applies also for zero F, zero z, empty schemes and p = 0. -/
theorem abelianHigherDirectImageRawPullback_identity {S Y : Scheme.{v}}
    (a : Y ⟶ Y) (ha : a = 𝟙 Y) (h : Y ⟶ S) (w : a ≫ h = h) (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ((a)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F)
    (hφ : HEq φ ((upperStarId AddCommGrpCat.{v + 1} Y).hom.app F))
    (U : S.Etale) (z : (abelianHigherDirectImageRawPresheaf h p F).obj (op U)) :
    abelianHigherDirectImageRawPullback a h h w p F F φ U z = z := by
  subst a
  have hφ' := eq_of_heq hφ
  subst φ
  unfold abelianHigherDirectImageRawPullback
  rw [upperStarComp_id_left]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_inv_app, Category.id_comp, Iso.symm_hom]
  exact Functor.identity_single_shift (upperStarId AddCommGrpCat.{v + 1} Y) _ F (p : ℤ) z

end AlgebraicGeometry.Etale
