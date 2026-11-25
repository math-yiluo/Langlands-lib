/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.Normalized.NormalizedDerivedUnitPasting
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraFrobenius

/-! # Pasting raw units with a nonexact first input -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

private lemma expand_raw_unit
    {C Y B : Type*} [Category C] [Category Y] [Category B]
    [Abelian C] [Abelian Y] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory Y] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions Y]
    (F : C ⥤ Y) (G : Y ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : HomotopyCategory C (.up ℤ))
    {Z : DerivedCategory B}
    (a : G.mapDerivedCategory.obj (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj K)) ⟶ Z)
    (b : DerivedCategory.Qh.obj ((G.mapHomotopyCategory (.up ℤ)).obj
      ((F.mapHomotopyCategory (.up ℤ)).obj K)) ⟶ Z)
    (h : (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F G).app K ≫ a = b) :
    G.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫ a =
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫ b := by
  have hh := congrArg (fun z ↦
    G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫ z) h
  simpa only [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app,
    comp_homotopy_inv, DerivedCategory.Qh.map_id, Category.id_comp,
    Category.assoc, Iso.hom_inv_id_app_assoc] using hh

/-- Raw homotopy units paste across a mixed exchange when the first input is right derived
and the second is exact. This is a categorical calculation, with no scheme, graph or chosen
compactification.

Source: Stacks Project, Tags 0F7B, 0F7J and 0D6E; the composition unit identity.
(blueprint: lem-pur-right-derived-raw-unit-pasting).

Proof in words: evaluate at a homotopy object and expand the exact-right composition unit.
Naturality moves the first unit and the first comparison through the second comparison.
Substitute the two normalization hypotheses. The exact functor's homotopy factor and its
inverse cancel. Move the ordinary first input map through the second map by naturality.
Apply the mixed-exchange unit equation at the image under J. The right-derived composition
unit identity then combines the P and S units. The exact triangle for H=J O removes the
remaining open-composition factors. On a representative complex, degreewise naturality
identifies the ordinary remaining map with t. All operations preserve zero maps, and the
identity exchange gives the ordinary composition-unit identity. No exactness of F is used. -/
theorem rightDerived_raw_unit_pasting
    {C U Y X Z B : Type*}
    [Category C] [Category U] [Category Y] [Category X] [Category Z] [Category B]
    [Abelian C] [Abelian U] [Abelian Y] [Abelian X] [Abelian Z] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory U] [HasDerivedCategory Y]
    [HasDerivedCategory X] [HasDerivedCategory Z] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions U]
    [Abelian.HasKInjectiveResolutions Y] [Abelian.HasKInjectiveResolutions X]
    [Abelian.HasKInjectiveResolutions Z]
    (J : C ⥤ U) (R : U ⥤ Y) (I : Y ⥤ Z) (O : U ⥤ X)
    (P : X ⥤ Z) (S : Z ⥤ B) (H : C ⥤ X) (W : X ⥤ B)
    (F : C ⥤ Y) (G : Y ⥤ B)
    [J.Additive] [R.Additive] [I.Additive] [O.Additive] [P.Additive] [S.Additive]
    [H.Additive] [W.Additive] [F.Additive] [G.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [P.PreservesKInjectiveComplexes]
    (ah : F ⟶ J ⋙ R) (ae : G ⟶ I ⋙ S)
    (γh : F.rightDerivedFunctor ⟶ J.mapDerivedCategory ⋙ R.rightDerivedFunctor)
    (γe : G.mapDerivedCategory ⟶ I.mapDerivedCategory ⋙ S.rightDerivedFunctor)
    (hγh : ∀ K : HomotopyCategory C (.up ℤ),
      F.rightDerivedFunctorUnit.app K ≫ γh.app (DerivedCategory.Qh.obj K) =
        DerivedCategory.Qh.map ((ah.mapHomotopyCategory (.up ℤ)).app K) ≫
          (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit J R).app K)
    (hγe : ∀ K : HomotopyCategory Y (.up ℤ),
      γe.app (DerivedCategory.Qh.obj K) =
        G.mapDerivedCategoryFactorsh.hom.app K ≫
          DerivedCategory.Qh.map ((ae.mapHomotopyCategory (.up ℤ)).app K) ≫
          (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit I S).app K)
    (χ : R ⋙ I ⟶ O ⋙ P)
    (Γ : R.rightDerivedFunctor ⋙ I.mapDerivedCategory ⟶
      O.mapDerivedCategory ⋙ P.rightDerivedFunctor)
    (hn : ∀ K : HomotopyCategory U (.up ℤ),
      I.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
          Γ.app (DerivedCategory.Qh.obj K) ≫
          P.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.hom.app K) =
        I.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ I)) (.up ℤ)).hom.app K ≫
              (χ.mapHomotopyCategory (.up ℤ)).app K ≫
              (Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ P)) (.up ℤ)).inv.app K) ≫
          P.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj K))
    (eo : H ≅ J ⋙ O) (ep : P ⋙ S ≅ W)
    (K : HomotopyCategory C (.up ℤ)) :
    let t : F ⋙ G ⟶ H ⋙ W :=
      Functor.whiskerRight ah G ≫ Functor.whiskerLeft J (Functor.whiskerLeft R ae) ≫
        Functor.whiskerLeft J (Functor.whiskerRight χ S) ≫
        Functor.whiskerLeft (J ⋙ O) ep.hom ≫ Functor.whiskerRight eo.inv W
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F G).app K ≫
        (Functor.whiskerRight γh G.mapDerivedCategory ≫
          Functor.whiskerLeft (J.mapDerivedCategory ⋙ R.rightDerivedFunctor) γe ≫
          Functor.whiskerLeft J.mapDerivedCategory (Functor.whiskerRight Γ S.rightDerivedFunctor) ≫
          Functor.whiskerLeft (J.mapDerivedCategory ⋙ O.mapDerivedCategory)
            (Functor.rightDerivedFunctorCompIso' P S ep).hom ≫
          Functor.whiskerRight (Functor.mapDerivedCategoryTriangleIso eo).inv
            W.rightDerivedFunctor).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((t.mapHomotopyCategory (.up ℤ)).app K) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit H W).app K := by
  intro t
  let α := (ah.mapHomotopyCategory (.up ℤ)).app K ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (J ⋙ R)) (.up ℤ)).inv.app K
  let γ := (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ I)) (.up ℤ)).hom.app
      ((J.mapHomotopyCategory (.up ℤ)).obj K) ≫
    (χ.mapHomotopyCategory (.up ℤ)).app ((J.mapHomotopyCategory (.up ℤ)).obj K) ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ P)) (.up ℤ)).inv.app
      ((J.mapHomotopyCategory (.up ℤ)).obj K)
  let κ := (Functor.mapHomotopyCategoryCompIso (Iso.refl (P ⋙ S)) (.up ℤ)).hom.app
      ((O.mapHomotopyCategory (.up ℤ)).obj ((J.mapHomotopyCategory (.up ℤ)).obj K)) ≫
    (ep.hom.mapHomotopyCategory (.up ℤ)).app
      ((O.mapHomotopyCategory (.up ℤ)).obj ((J.mapHomotopyCategory (.up ℤ)).obj K))
  let w := (eo.hom.mapHomotopyCategory (.up ℤ)).app K ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (J ⋙ O)) (.up ℤ)).inv.app K
  let ta := Functor.whiskerRight ah G ≫ Functor.whiskerLeft J (Functor.whiskerLeft R ae) ≫
    Functor.whiskerLeft J (Functor.whiskerRight χ S) ≫
    Functor.whiskerLeft (J ⋙ O) ep.hom ≫ Functor.whiskerRight eo.inv W
  have ht : (ta.mapHomotopyCategory (.up ℤ)).app K ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ W)) (.up ℤ)).inv.app K ≫
      (W.mapHomotopyCategory (.up ℤ)).map w =
      (ae.mapHomotopyCategory (.up ℤ)).app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (I ⋙ S)) (.up ℤ)).inv.app
          ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        (S.mapHomotopyCategory (.up ℤ)).map
          ((I.mapHomotopyCategory (.up ℤ)).map α ≫ γ) ≫ κ := by
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    have hz : (ta.mapHomologicalComplex (.up ℤ)).app L ≫
        (W.mapHomologicalComplex (.up ℤ)).map
          ((eo.hom.mapHomologicalComplex (.up ℤ)).app L) =
        (ae.mapHomologicalComplex (.up ℤ)).app ((F.mapHomologicalComplex (.up ℤ)).obj L) ≫
          (S.mapHomologicalComplex (.up ℤ)).map
            ((I.mapHomologicalComplex (.up ℤ)).map
                ((ah.mapHomologicalComplex (.up ℤ)).app L) ≫
              (χ.mapHomologicalComplex (.up ℤ)).app
                ((J.mapHomologicalComplex (.up ℤ)).obj L)) ≫
          (ep.hom.mapHomologicalComplex (.up ℤ)).app
            ((O.mapHomologicalComplex (.up ℤ)).obj
              ((J.mapHomologicalComplex (.up ℤ)).obj L)) := by
      ext n
      simp only [ta, NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.comp_f,
        Functor.mapHomologicalComplex_map_f, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
        Category.assoc]
      rw [← W.map_comp, eo.inv_hom_id_app]
      erw [W.map_id, Category.comp_id]
      have hna := ae.naturality (ah.app (L.X n))
      dsimp only [Functor.comp_map, Functor.comp_obj] at hna
      rw [reassoc_of% hna]
      simp only [Functor.map_comp, Category.assoc]
      rfl
    have hh := (HomotopyCategory.quotient B (.up ℤ)).congr_map hz
    simp only [Functor.map_comp] at hh
    simp only [α, γ, κ, w, comp_homotopy_inv,
      Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp,
      Category.comp_id, Functor.map_comp]
    convert hh using 1 <;> rfl
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app]
  simp only [comp_homotopy_inv, DerivedCategory.Qh.map_id, Category.id_comp, Category.assoc]
  rw [← G.mapDerivedCategory.map_comp_assoc, hγh]
  let v := DerivedCategory.Qh.map ((ah.mapHomotopyCategory (.up ℤ)).app K) ≫
    (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit J R).app K
  change G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
    G.mapDerivedCategory.map v ≫ _ = _
  have hv := γe.naturality v
  dsimp only [Functor.comp_map, Functor.comp_obj] at hv
  dsimp only [Functor.comp_obj]
  erw [reassoc_of% hv, hγe]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [v, Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app,
    Functor.map_comp, Category.assoc]
  let da := Functor.mapDerivedCategoryTriangleIso eo
  let z := O.mapDerivedCategory.map (J.mapDerivedCategoryFactorsh.hom.app K) ≫
    O.mapDerivedCategoryFactorsh.hom.app ((J.mapHomotopyCategory (.up ℤ)).obj K)
  apply (cancel_mono (W.rightDerivedFunctor.map
    (da.hom.app (DerivedCategory.Qh.obj K) ≫ z))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [← W.rightDerivedFunctor.map_comp_assoc]
  erw [Iso.inv_hom_id_app, W.rightDerivedFunctor.map_id, Category.id_comp]
  have hc := (Functor.rightDerivedFunctorCompIso' P S ep).hom.naturality z
  dsimp only [Functor.comp_map, Functor.comp_obj] at hc
  rw [← hc]
  simp only [z, Functor.map_comp, Category.assoc]
  have hg := Γ.naturality (J.mapDerivedCategoryFactorsh.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hg
  simp only [← S.rightDerivedFunctor.map_comp_assoc]
  rw [← reassoc_of% hg]
  simp only [← I.mapDerivedCategory.map_comp_assoc,
    ← R.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app]
  erw [R.rightDerivedFunctor.map_id]
  simp only [I.mapDerivedCategory.map_comp, Category.assoc]
  have hi := I.mapDerivedCategoryFactorsh.inv.naturality
    ((ah.mapHomotopyCategory (.up ℤ)).app K ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (J ⋙ R)) (.up ℤ)).inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hi
  simp only [Functor.map_comp] at hi
  rw [← reassoc_of% hi]
  erw [I.mapDerivedCategory.map_id, Category.id_comp]
  erw [hn ((J.mapHomotopyCategory (.up ℤ)).obj K)]
  rw [Iso.inv_hom_id_app_assoc]
  simp only [← DerivedCategory.Qh.map_comp_assoc,
    ← (I.mapHomotopyCategory (.up ℤ)).map_comp_assoc]
  rw [S.rightDerivedFunctor.map_comp]
  simp only [Category.assoc]
  have hs := S.rightDerivedFunctorUnit.naturality
    ((I.mapHomotopyCategory (.up ℤ)).map α ≫ γ)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hs
  erw [← reassoc_of% hs,
    right_comp_unit P S ep
      ((O.mapHomotopyCategory (.up ℤ)).obj ((J.mapHomotopyCategory (.up ℤ)).obj K))]
  simp only [← W.rightDerivedFunctor.map_comp]
  erw [Functor.mapDerivedCategoryTriangleIso_hom_app_Qh_obj eo K]
  have hw := W.rightDerivedFunctorUnit.naturality w
  dsimp only [Functor.comp_map, Functor.comp_obj] at hw
  rw [← hw]
  simp only [Category.assoc, ← DerivedCategory.Qh.map_comp_assoc]
  rw [ht]

private lemma rightDerived_raw_unit_pasting_of_eq
    {C U Y X Z B : Type*}
    [Category C] [Category U] [Category Y] [Category X] [Category Z] [Category B]
    [Abelian C] [Abelian U] [Abelian Y] [Abelian X] [Abelian Z] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory U] [HasDerivedCategory Y]
    [HasDerivedCategory X] [HasDerivedCategory Z] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions U]
    [Abelian.HasKInjectiveResolutions Y] [Abelian.HasKInjectiveResolutions X]
    [Abelian.HasKInjectiveResolutions Z]
    (J : C ⥤ U) (R : U ⥤ Y) (I : Y ⥤ Z) (O : U ⥤ X)
    (P : X ⥤ Z) (S : Z ⥤ B) (H : C ⥤ X) (W : X ⥤ B)
    (F : C ⥤ Y) (G : Y ⥤ B)
    [J.Additive] [R.Additive] [I.Additive] [O.Additive] [P.Additive] [S.Additive]
    [H.Additive] [W.Additive] [F.Additive] [G.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [P.PreservesKInjectiveComplexes]
    (ah : F ⟶ J ⋙ R) (ae : G ⟶ I ⋙ S)
    (γh : F.rightDerivedFunctor ⟶ J.mapDerivedCategory ⋙ R.rightDerivedFunctor)
    (γe : G.mapDerivedCategory ⟶ I.mapDerivedCategory ⋙ S.rightDerivedFunctor)
    (hγh : ∀ K : HomotopyCategory C (.up ℤ),
      F.rightDerivedFunctorUnit.app K ≫ γh.app (DerivedCategory.Qh.obj K) =
        DerivedCategory.Qh.map ((ah.mapHomotopyCategory (.up ℤ)).app K) ≫
          (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit J R).app K)
    (hγe : ∀ K : HomotopyCategory Y (.up ℤ),
      γe.app (DerivedCategory.Qh.obj K) =
        G.mapDerivedCategoryFactorsh.hom.app K ≫
          DerivedCategory.Qh.map ((ae.mapHomotopyCategory (.up ℤ)).app K) ≫
          (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit I S).app K)
    (χ : R ⋙ I ⟶ O ⋙ P)
    (Γ : R.rightDerivedFunctor ⋙ I.mapDerivedCategory ⟶
      O.mapDerivedCategory ⋙ P.rightDerivedFunctor)
    (hn : ∀ K : HomotopyCategory U (.up ℤ),
      I.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
          Γ.app (DerivedCategory.Qh.obj K) ≫
          P.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.hom.app K) =
        I.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ I)) (.up ℤ)).hom.app K ≫
              (χ.mapHomotopyCategory (.up ℤ)).app K ≫
              (Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ P)) (.up ℤ)).inv.app K) ≫
          P.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj K))
    (eo : H ≅ J ⋙ O) (ep : P ⋙ S ≅ W)
    (t : F ⋙ G ⟶ H ⋙ W)
    (ht : t = Functor.whiskerRight ah G ≫ Functor.whiskerLeft J (Functor.whiskerLeft R ae) ≫
        Functor.whiskerLeft J (Functor.whiskerRight χ S) ≫
        Functor.whiskerLeft (J ⋙ O) ep.hom ≫ Functor.whiskerRight eo.inv W)
    (K : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F G).app K ≫
        (Functor.whiskerRight γh G.mapDerivedCategory ≫
          Functor.whiskerLeft (J.mapDerivedCategory ⋙ R.rightDerivedFunctor) γe ≫
          Functor.whiskerLeft J.mapDerivedCategory (Functor.whiskerRight Γ S.rightDerivedFunctor) ≫
          Functor.whiskerLeft (J.mapDerivedCategory ⋙ O.mapDerivedCategory)
            (Functor.rightDerivedFunctorCompIso' P S ep).hom ≫
          Functor.whiskerRight (Functor.mapDerivedCategoryTriangleIso eo).inv
            W.rightDerivedFunctor).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((t.mapHomotopyCategory (.up ℤ)).app K) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit H W).app K := by
  have h := rightDerived_raw_unit_pasting J R I O P S H W F G ah ae γh γe
    hγh hγe χ Γ hn eo ep K
  have he := congrArg (fun z : F ⋙ G ⟶ H ⋙ W ↦
    DerivedCategory.Qh.map ((z.mapHomotopyCategory (.up ℤ)).app K) ≫
      (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit H W).app K) ht
  exact h.trans he.symm

private lemma rightDerived_raw_unit_pasting_tower_app
    {C U Y X Z B : Type*}
    [Category C] [Category U] [Category Y] [Category X] [Category Z] [Category B]
    [Abelian C] [Abelian U] [Abelian Y] [Abelian X] [Abelian Z] [Abelian B]
    [dcC : HasDerivedCategory C] [dcU : HasDerivedCategory U] [dcY : HasDerivedCategory Y]
    [dcX : HasDerivedCategory X] [dcZ : HasDerivedCategory Z] [dcB : HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions U]
    [Abelian.HasKInjectiveResolutions Y] [Abelian.HasKInjectiveResolutions X]
    [Abelian.HasKInjectiveResolutions Z]
    (J : C ⥤ U) (R : U ⥤ Y) (I : Y ⥤ Z) (O : U ⥤ X)
    (P : X ⥤ Z) (S : Z ⥤ B) (H : C ⥤ X) (W : X ⥤ B)
    (F : C ⥤ Y) (G : Y ⥤ B)
    [jadd : J.Additive] [radd : R.Additive] [iadd : I.Additive]
    [oadd : O.Additive] [padd : P.Additive] [sadd : S.Additive]
    [hadd : H.Additive] [wadd : W.Additive] [fadd : F.Additive] [gadd : G.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [P.PreservesKInjectiveComplexes]
    (ah : F ⟶ J ⋙ R) (ae : G ⟶ I ⋙ S)
    (γh : F.rightDerivedFunctor ⟶ J.mapDerivedCategory ⋙ R.rightDerivedFunctor)
    (γe : G.mapDerivedCategory ⟶ I.mapDerivedCategory ⋙ S.rightDerivedFunctor)
    (hγh : ∀ K : HomotopyCategory C (.up ℤ),
      F.rightDerivedFunctorUnit.app K ≫ γh.app (DerivedCategory.Qh.obj K) =
        DerivedCategory.Qh.map ((ah.mapHomotopyCategory (.up ℤ)).app K) ≫
          (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit J R).app K)
    (hγe : ∀ K : HomotopyCategory Y (.up ℤ),
      γe.app (DerivedCategory.Qh.obj K) =
        G.mapDerivedCategoryFactorsh.hom.app K ≫
          DerivedCategory.Qh.map ((ae.mapHomotopyCategory (.up ℤ)).app K) ≫
          (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit I S).app K)
    (χ : R ⋙ I ⟶ O ⋙ P)
    (Γ : R.rightDerivedFunctor ⋙ I.mapDerivedCategory ⟶
      O.mapDerivedCategory ⋙ P.rightDerivedFunctor)
    (hn : ∀ K : HomotopyCategory U (.up ℤ),
      I.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
          Γ.app (DerivedCategory.Qh.obj K) ≫
          P.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.hom.app K) =
        I.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ I)) (.up ℤ)).hom.app K ≫
              (χ.mapHomotopyCategory (.up ℤ)).app K ≫
              (Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ P)) (.up ℤ)).inv.app K) ≫
          P.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj K))
    (eo : H ≅ J ⋙ O) (ep : P ⋙ S ≅ W)
    (t : F ⋙ G ⟶ H ⋙ W)
    (ht : t = Functor.whiskerRight ah G ≫ Functor.whiskerLeft J (Functor.whiskerLeft R ae) ≫
        Functor.whiskerLeft J (Functor.whiskerRight χ S) ≫
        Functor.whiskerLeft (J ⋙ O) ep.hom ≫ Functor.whiskerRight eo.inv W)
    (K : HomotopyCategory C (.up ℤ))
    (D : (J.mapDerivedCategory ⋙ R.rightDerivedFunctor) ⋙
        (I.mapDerivedCategory ⋙ S.rightDerivedFunctor) ⟶
      H.mapDerivedCategory ⋙ W.rightDerivedFunctor)
    (hD : D.app (DerivedCategory.Qh.obj K) =
      S.rightDerivedFunctor.map (Γ.app (J.mapDerivedCategory.obj (DerivedCategory.Qh.obj K))) ≫
        (Functor.rightDerivedFunctorCompIso' P S ep).hom.app
          ((J.mapDerivedCategory ⋙ O.mapDerivedCategory).obj (DerivedCategory.Qh.obj K)) ≫
        W.rightDerivedFunctor.map
          ((Functor.mapDerivedCategoryTriangleIso eo).inv.app (DerivedCategory.Qh.obj K))) :
    G.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫
        G.mapDerivedCategory.map (γh.app (DerivedCategory.Qh.obj K)) ≫
        γe.app ((J.mapDerivedCategory ⋙ R.rightDerivedFunctor).obj (DerivedCategory.Qh.obj K)) ≫
        D.app (DerivedCategory.Qh.obj K) =
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((t.mapHomotopyCategory (.up ℤ)).app K) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit H W).app K := by
  rw [hD]
  have hu := rightDerived_raw_unit_pasting_of_eq J R I O P S H W F G ah ae γh γe
    hγh hγe χ Γ hn eo ep t ht K
  have hh := expand_raw_unit F G K _ _ hu
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] using hh

private noncomputable def pasteDerivedTower
    {C U Y X Z B : Type*}
    [Category C] [Category U] [Category Y] [Category X] [Category Z] [Category B]
    [Abelian C] [Abelian U] [Abelian Y] [Abelian X] [Abelian Z] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory U] [HasDerivedCategory Y]
    [HasDerivedCategory X] [HasDerivedCategory Z] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions U] [Abelian.HasKInjectiveResolutions X]
    [Abelian.HasKInjectiveResolutions Z]
    (J : C ⥤ U) (R : U ⥤ Y) (I : Y ⥤ Z) (O : U ⥤ X)
    (P : X ⥤ Z) (S : Z ⥤ B) (H : C ⥤ X) (T : X ⥤ B)
    [J.Additive] [R.Additive] [I.Additive] [O.Additive] [P.Additive] [S.Additive]
    [H.Additive] [T.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [P.PreservesKInjectiveComplexes]
    (Γ : R.rightDerivedFunctor ⋙ I.mapDerivedCategory ⟶
      O.mapDerivedCategory ⋙ P.rightDerivedFunctor)
    (eo : H ≅ J ⋙ O) (ep : P ⋙ S ≅ T) :
    (J.mapDerivedCategory ⋙ R.rightDerivedFunctor) ⋙
        (I.mapDerivedCategory ⋙ S.rightDerivedFunctor) ⟶
      H.mapDerivedCategory ⋙ T.rightDerivedFunctor :=
  Functor.whiskerLeft J.mapDerivedCategory (Functor.whiskerRight Γ S.rightDerivedFunctor) ≫
    Functor.whiskerLeft (J.mapDerivedCategory ⋙ O.mapDerivedCategory)
      (Functor.rightDerivedFunctorCompIso' P S ep).hom ≫
    Functor.whiskerRight (Functor.mapDerivedCategoryTriangleIso eo).inv T.rightDerivedFunctor

attribute [local irreducible] pasteDerivedTower

private lemma pasteDerivedTower_app
    {C U Y X Z B : Type*}
    [Category C] [Category U] [Category Y] [Category X] [Category Z] [Category B]
    [Abelian C] [Abelian U] [Abelian Y] [Abelian X] [Abelian Z] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory U] [HasDerivedCategory Y]
    [HasDerivedCategory X] [HasDerivedCategory Z] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions U] [Abelian.HasKInjectiveResolutions X]
    [Abelian.HasKInjectiveResolutions Z]
    (J : C ⥤ U) (R : U ⥤ Y) (I : Y ⥤ Z) (O : U ⥤ X)
    (P : X ⥤ Z) (S : Z ⥤ B) (H : C ⥤ X) (T : X ⥤ B)
    [J.Additive] [R.Additive] [I.Additive] [O.Additive] [P.Additive] [S.Additive]
    [H.Additive] [T.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [P.PreservesKInjectiveComplexes]
    (Γ : R.rightDerivedFunctor ⋙ I.mapDerivedCategory ⟶
      O.mapDerivedCategory ⋙ P.rightDerivedFunctor)
    (eo : H ≅ J ⋙ O) (ep : P ⋙ S ≅ T)
    (K : DerivedCategory C) :
    (pasteDerivedTower J R I O P S H T Γ eo ep).app K =
      S.rightDerivedFunctor.map (Γ.app (J.mapDerivedCategory.obj K)) ≫
        (Functor.rightDerivedFunctorCompIso' P S ep).hom.app
          ((J.mapDerivedCategory ⋙ O.mapDerivedCategory).obj K) ≫
        T.rightDerivedFunctor.map ((Functor.mapDerivedCategoryTriangleIso eo).inv.app K) := by
  unfold pasteDerivedTower
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]

end AlgebraicGeometry.Etale
