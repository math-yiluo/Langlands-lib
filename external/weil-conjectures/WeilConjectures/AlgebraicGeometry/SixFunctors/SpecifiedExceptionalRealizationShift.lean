/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
public import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
import all WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift

/-! # Right realization shifts determined by the specified relative Hom chain

## References

* Zheng, Proposition 2.23
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u vC uC vD uD
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

private theorem exactCompatibility_shift
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    NatTrans.CommShift F.mapDerivedCategoryPlusCompatibility.hom ℤ := by
  change NatTrans.CommShift
    (DerivedCategory.TStructure.t.plus.liftCompιIso
      (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory)
      (fun X ↦ (F.mapDerivedCategoryPlus.obj X).2)).hom ℤ
  infer_instance

attribute [local instance] exactCompatibility_shift
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem rightDerivedCompatibility_shift
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [EnoughInjectives A] [CategoryTheory.Abelian.HasKInjectiveResolutions A]
    (R : A ⥤ B) [R.Additive] [R.rightDerivedFunctor.CommShift ℤ]
    [NatTrans.CommShift R.rightDerivedFunctorUnit ℤ] :
    NatTrans.CommShift R.rightDerivedFunctorPlusCompatibility.hom ℤ := by
  let τ := R.rightDerivedFunctorPlusCompatibility.hom
  let α := R.rightDerivedFunctorPlusιUnit
  let β := R.ιRightDerivedFunctorUnit
  have hfac : α ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh τ = β := by
    ext K
    simp [α, β, τ, Functor.rightDerivedFunctorPlusCompatibility]
  have hα : NatTrans.CommShift α ℤ := by
    have he : α =
        (Functor.associator R.mapHomotopyCategoryPlus
          DerivedCategory.Plus.Qh DerivedCategory.Plus.ι).inv ≫
        Functor.whiskerRight R.rightDerivedFunctorPlusUnith DerivedCategory.Plus.ι ≫
        (Functor.associator DerivedCategory.Plus.Qh
          R.rightDerivedFunctorPlus DerivedCategory.Plus.ι).hom := by
      ext K
      simp [α, Functor.rightDerivedFunctorPlusιUnit]
    rw [he]
    infer_instance
  let qA : DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι ≅
      HomotopyCategory.Plus.ι A ⋙ DerivedCategory.Qh :=
    DerivedCategory.TStructure.t.plus.liftCompιIso
      (HomotopyCategory.Plus.ι A ⋙ DerivedCategory.Qh)
      (fun X ↦ (DerivedCategory.Plus.Qh.obj X).2)
  let qB : DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι ≅
      HomotopyCategory.Plus.ι B ⋙ DerivedCategory.Qh :=
    DerivedCategory.TStructure.t.plus.liftCompιIso
      (HomotopyCategory.Plus.ι B ⋙ DerivedCategory.Qh)
      (fun X ↦ (DerivedCategory.Plus.Qh.obj X).2)
  let hR : R.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι B ≅
      HomotopyCategory.Plus.ι A ⋙ R.mapHomotopyCategory (.up ℤ) :=
    (HomotopyCategory.plus B).liftCompιIso
      (HomotopyCategory.Plus.ι A ⋙ R.mapHomotopyCategory (.up ℤ))
      (fun X ↦ (R.mapHomotopyCategoryPlus.obj X).2)
  have hqA : NatTrans.CommShift qA.hom ℤ := by dsimp [qA]; infer_instance
  have hqB : NatTrans.CommShift qB.hom ℤ := by dsimp [qB]; infer_instance
  have hhR : NatTrans.CommShift hR.hom ℤ := by dsimp [hR]; infer_instance
  have hβ : NatTrans.CommShift β ℤ := by
    have he : β =
        Functor.whiskerLeft R.mapHomotopyCategoryPlus qB.hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight hR.hom DerivedCategory.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (HomotopyCategory.Plus.ι A) R.rightDerivedFunctorUnit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight qA.inv R.rightDerivedFunctor ≫
        (Functor.associator _ _ _).hom := by
      ext K
      simp only [β, Functor.ιRightDerivedFunctorUnit, qA, qB, hR,
        ObjectProperty.liftCompιIso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
        Functor.comp_obj, ObjectProperty.ι_obj, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
        Functor.associator_hom_app, Category.comp_id, Category.id_comp]
      erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp,
        R.rightDerivedFunctor.map_id, Category.comp_id]
    rw [he]
    infer_instance
  let inj := (InjectiveObject.ι A).mapHomotopyCategoryPlus
  have : IsIso (Functor.whiskerLeft inj α) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun K ↦ ?_)
    dsimp [α, Functor.rightDerivedFunctorPlusιUnit]
    infer_instance
  have : NatTrans.CommShift (Functor.whiskerLeft inj
      (Functor.whiskerLeft DerivedCategory.Plus.Qh τ)) ℤ := by
    have he : Functor.whiskerLeft inj
        (Functor.whiskerLeft DerivedCategory.Plus.Qh τ) =
        inv (Functor.whiskerLeft inj α) ≫ Functor.whiskerLeft inj β := by
      rw [IsIso.eq_inv_comp, ← Functor.whiskerLeft_comp, hfac]
    rw [he]
    have : NatTrans.CommShift (inv (Functor.whiskerLeft inj α)) ℤ :=
      NatTrans.CommShift.of_isIso _ _
    infer_instance
  have : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Plus.Qh τ) ℤ := by
    refine NatTrans.CommShift.of_whiskerLeft _ inj (fun K ↦ ?_)
    let E := DerivedCategory.Plus.injectiveObjectEquivalence A
    obtain ⟨f, hf⟩ := (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective K
      (inj.obj (E.inverse.obj (DerivedCategory.Plus.Qh.obj K)))
      inferInstance).2 (E.counitIso.inv.app (DerivedCategory.Plus.Qh.obj K))
    refine ⟨_, f, ?_⟩
    rw [Functor.comp_map, hf]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Plus.Qh fun K ↦
    ⟨_, (DerivedCategory.Plus.Qh.objObjPreimageIso K).inv, inferInstance⟩

private theorem fixedComparison_shift
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    NatTrans.CommShift (fixedCompactSupportComparisonIso Λ c).hom ℤ := by
  have := c.isProper
  let : (Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) c.g).CommShift ℤ :=
    inferInstanceAs
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctorPlus.CommShift ℤ)
  have huEt : NatTrans.CommShift
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctorUnit ℤ :=
    Etale.commShift_rightDerivedLowerStarUnit _ _
  have huPro : NatTrans.CommShift
      (lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctorUnit ℤ :=
    CategoryTheory.canonical_unit_commShift _
  have hcEt : NatTrans.CommShift
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctorPlusCompatibility.hom ℤ :=
    rightDerivedCompatibility_shift _
  have hcPro : NatTrans.CommShift
      (lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctorPlusCompatibility.hom ℤ :=
    rightDerivedCompatibility_shift _
  have : NatTrans.CommShift (fixedComparisonDirectImageMatePlus Λ c.g) ℤ := by
    dsimp only [fixedComparisonDirectImageMatePlus]
    infer_instance
  have hIso : IsIso (fixedComparisonDirectImageMatePlus Λ c.g) :=
    isIso_fixedComparisonDirectImageMatePlus Λ c.g
  let d :=
    (Functor.associator DerivedCategory.Plus.ι
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctor
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctorPlusCompatibility.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctorPlus
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategoryPlusCompatibility.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (asIso (fixedComparisonDirectImageMatePlus Λ c.g)) DerivedCategory.Plus.ι ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) c.Z).mapDerivedCategoryPlus
      (lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctorPlusCompatibility ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) c.Z).mapDerivedCategoryPlusCompatibility _ ≪≫
    Functor.associator _ _ _
  have hd : NatTrans.CommShift (fixedDirectImageComparisonIso Λ c.g).hom ℤ := by
    have he : (fixedDirectImageComparisonIso Λ c.g).hom = d.hom := by
      ext K
      simp [d, fixedDirectImageComparisonIso, Functor.comp_obj]
    rw [he]
    simp only [d, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, asIso_hom]
    apply NatTrans.CommShift.comp
  simp only [fixedCompactSupportComparisonIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  dsimp only [rightDerivedLowerShriekOfCompactification]
  apply NatTrans.CommShift.comp

private theorem derivedComparison_shift
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).CommShift ℤ := by
  have he : derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X =
      (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryRightDerivedAdjunction := by
    let ad := comparisonAdjunction (ModuleCat.{u + 1} Λ) X
    let iso :=
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).leftDerivedFunctorIsoMapDerivedCategory
    have hd : ad.derivedAdjunction =
        ad.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft iso.symm := by
      have hf := Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
      exact Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _ iso hf.symm
    apply Adjunction.ext
    change (ad.derivedAdjunction.ofNatIsoLeft iso).unit = _
    rw [hd]
    ext M
    simp [Adjunction.ofNatIsoLeft_unit, ← Functor.map_comp, Category.assoc, ad]
  rw [he]
  exact canonicalRightDerivedAdjunctionShift (comparisonAdjunction (ModuleCat.{u + 1} Λ) X)

private theorem adjHom_shift
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    {P : A ⥤ B} {H : B ⥤ A} [P.CommShift ℤ] [H.CommShift ℤ]
    (adj : P ⊣ H) [adj.CommShift ℤ] (n : ℤ) {M : A} {N : B}
    (a : P.obj M ⟶ N) :
    adj.homEquiv _ _ ((P.commShiftIso n).hom.app M ≫ a⟦n⟧') =
      (adj.homEquiv M N a)⟦n⟧' ≫ (H.commShiftIso n).inv.app N := by
  apply (cancel_mono ((H.commShiftIso n).hom.app N)).1
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
  rw [Functor.commShiftIso_hom_naturality]
  have hu := adj.unit_app_commShiftIso_hom_app ℤ n M
  simp only [Functor.commShiftIso_comp_hom_app] at hu
  simpa only [Functor.map_comp, Category.comp_id, Category.assoc] using
    congrArg (fun b ↦ b ≫ (H.map a)⟦n⟧') hu

private theorem commShift_assoc_inv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ] (n : ℤ) (X : A) :
    (((F ⋙ G) ⋙ H).commShiftIso n).inv.app X =
      ((F ⋙ G ⋙ H).commShiftIso n).inv.app X := by
  simp only [Functor.commShiftIso_comp_inv_app, Functor.map_comp,
    Functor.comp_map, Functor.comp_obj, Category.assoc]

private def relativeHom
    {S A B D : Type*} [Category S] [Category A] [Category B] [Category D]
    (I : S ⥤ A) (U : A ⥤ B) (P : B ⥤ D) {Q : A ⥤ D} {R : D ⥤ A}
    (adj : Q ⊣ R) (e : I ⋙ U ⋙ P ≅ I ⋙ Q)
    (Z : S) {M : B} (w : (I ⋙ U).obj Z ≅ M) {N : D} (a : P.obj M ⟶ N) :
    M ⟶ (R ⋙ U).obj N :=
  w.inv ≫ U.map (adj.homEquiv _ _ (e.inv.app Z ≫ P.map w.hom ≫ a))

private theorem relativeHom_shift
    {S A B D : Type*} [Category S] [Category A] [Category B] [Category D]
    [HasShift S ℤ] [HasShift A ℤ] [HasShift B ℤ] [HasShift D ℤ]
    (I : S ⥤ A) (U : A ⥤ B) (P : B ⥤ D) {Q : A ⥤ D} {R : D ⥤ A}
    [I.CommShift ℤ] [U.CommShift ℤ] [P.CommShift ℤ]
    [Q.CommShift ℤ] [R.CommShift ℤ] (adj : Q ⊣ R) [adj.CommShift ℤ]
    (e : I ⋙ U ⋙ P ≅ I ⋙ Q) [e.hom.CommShift ℤ]
    (n : ℤ) (Z : S) {M M' : B} (w : (I ⋙ U).obj Z ≅ M)
    {N N' : D} (s : M' ≅ M⟦n⟧) (t : N' ≅ N⟦n⟧) (a : P.obj M ⟶ N) :
    let w' := ((I ⋙ U).commShiftIso n).app Z ≪≫ (shiftFunctor B n).mapIso w ≪≫ s.symm
    relativeHom I U P adj e (Z⟦n⟧) w'
      (P.map s.hom ≫ (P.commShiftIso n).hom.app M ≫ a⟦n⟧' ≫ t.inv) =
    s.hom ≫ (relativeHom I U P adj e Z w a)⟦n⟧' ≫
      ((R ⋙ U).commShiftIso n).inv.app N ≫ (R ⋙ U).map t.inv := by
  intro w'
  let b := e.inv.app Z ≫ P.map w.hom ≫ a
  have he : e.inv.app (Z⟦n⟧) ≫ P.map (((I ⋙ U).commShiftIso n).hom.app Z) ≫
      (P.commShiftIso n).hom.app ((I ⋙ U).obj Z) =
      Q.map ((I.commShiftIso n).hom.app Z) ≫
        (Q.commShiftIso n).hom.app (I.obj Z) ≫ (e.inv.app Z)⟦n⟧' := by
    simpa only [Functor.commShiftIso_comp_hom_app, Functor.map_comp,
      Functor.comp_map, Functor.comp_obj, Category.assoc] using
      (NatTrans.shift_app_comm e.inv n Z).symm
  have hb : e.inv.app (Z⟦n⟧) ≫ P.map w'.hom ≫
      (P.map s.hom ≫ (P.commShiftIso n).hom.app M ≫ a⟦n⟧' ≫ t.inv) =
      Q.map ((I.commShiftIso n).hom.app Z) ≫
        (Q.commShiftIso n).hom.app (I.obj Z) ≫ b⟦n⟧' ≫ t.inv := by
    dsimp only [w', Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
    simp only [Functor.map_comp, Functor.comp_obj, Category.assoc]
    simp only [Functor.comp_obj] at he
    rw [← P.map_comp_assoc s.inv s.hom, s.inv_hom_id, P.map_id, Category.id_comp,
      Functor.commShiftIso_hom_naturality_assoc, reassoc_of% he]
    simp only [b, Functor.map_comp, Category.assoc]
  change w'.inv ≫ U.map (adj.homEquiv _ _ _) = _
  rw [hb, adj.homEquiv_naturality_left, ← Category.assoc,
    adj.homEquiv_naturality_right]
  simp only [Functor.comp_obj]
  rw [adjHom_shift adj n]
  dsimp only [w', relativeHom, Iso.trans_inv, Iso.symm_inv, Iso.app_inv,
    Functor.mapIso_inv, Functor.comp_map]
  simp only [Functor.commShiftIso_comp_inv_app, Functor.map_comp, Category.assoc]
  rw [← U.map_comp_assoc, Iso.inv_hom_id_app]
  erw [U.map_id, Category.id_comp]
  rw [← Functor.commShiftIso_inv_naturality_assoc]

private theorem normalizedCounit_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (RX : C ⥤ A) (RY : D ⥤ B) (G : D ⥤ C) (H : B ⥤ A)
    [RX.CommShift ℤ] [RY.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (r : G ⋙ RX ≅ RY ⋙ H) (n : ℤ) (L : D)
    (h : RX.map ((G.commShiftIso n).inv.app L) ≫ r.hom.app (L⟦n⟧) =
      (RX.commShiftIso n).hom.app (G.obj L) ≫ (r.hom.app L)⟦n⟧' ≫
        (H.commShiftIso n).inv.app (RY.obj L) ≫
          H.map ((RY.commShiftIso n).inv.app L)) :
    ((G ⋙ RX).commShiftIso n).hom.app L ≫ (r.hom.app L)⟦n⟧' =
      r.hom.app (L⟦n⟧) ≫ ((RY ⋙ H).commShiftIso n).hom.app L := by
  rw [Functor.commShiftIso_comp_hom_app G RX, Functor.commShiftIso_comp_hom_app RY H]
  simp only [Category.assoc]
  apply (cancel_epi (RX.map ((G.commShiftIso n).inv.app L))).1
  rw [← RX.map_comp_assoc, Iso.inv_hom_id_app, RX.map_id, Category.id_comp,
    reassoc_of% h]
  rw [← H.map_comp_assoc, Iso.inv_hom_id_app]
  erw [H.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

private theorem relativeRealization_shift
    {S A B E T C D : Type*}
    [Category S] [Category A] [Category B] [Category E] [Category T]
    [Category C] [Category D]
    [HasShift S ℤ] [HasShift A ℤ] [HasShift B ℤ] [HasShift E ℤ] [HasShift T ℤ]
    [HasShift C ℤ] [HasShift D ℤ]
    (I : S ⥤ A) (U : A ⥤ B) (P : B ⥤ T)
    {Q : A ⥤ E} {R : E ⥤ A} {V : E ⥤ T} {W : T ⥤ E}
    [I.CommShift ℤ] [U.CommShift ℤ] [P.CommShift ℤ]
    [Q.CommShift ℤ] [R.CommShift ℤ] [V.CommShift ℤ] [W.CommShift ℤ]
    (a₁ : Q ⊣ R) (a₂ : V ⊣ W) [a₁.CommShift ℤ] [a₂.CommShift ℤ]
    (e : I ⋙ U ⋙ P ≅ I ⋙ Q ⋙ V) [e.hom.CommShift ℤ]
    (RX : C ⥤ B) (RY : D ⥤ T) [RX.CommShift ℤ] [RY.CommShift ℤ]
    (F : C ⥤ D) (G : D ⥤ C) [F.CommShift ℤ] (adj : F ⊣ G)
    (rF : F ⋙ RY ≅ RX ⋙ P) (rG : G ⋙ RX ≅ RY ⋙ W ⋙ R ⋙ U)
    [rF.hom.CommShift ℤ]
    (origin : ∀ K, ∃ Z : S, Nonempty ((I ⋙ U).obj Z ≅ RX.obj K))
    (hn : ∀ K L (Z : S) (w : (I ⋙ U).obj Z ≅ RX.obj K) (a : F.obj K ⟶ L),
      RX.map (adj.homEquiv K L a) ≫ rG.hom.app L =
        relativeHom I U P (a₁.comp a₂) e Z w (rF.inv.app K ≫ RY.map a)) :
    letI := adj.rightAdjointCommShift ℤ
    rG.hom.CommShift ℤ := by
  let := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  let H := W ⋙ R ⋙ U
  let ac := a₁.comp a₂
  constructor
  intro n
  ext L
  let K := G.obj L
  obtain ⟨Z, ⟨w⟩⟩ := origin K
  let wn := ((I ⋙ U).commShiftIso n).app Z ≪≫
    (shiftFunctor B n).mapIso w ≪≫ (RX.commShiftIso n).symm.app K
  have h := relativeHom_shift I U P ac e n Z w
    ((RX.commShiftIso n).app K) ((RY.commShiftIso n).app L)
    (rF.inv.app K ≫ RY.map (adj.counit.app L))
  rw [commShift_assoc_inv] at h
  change relativeHom I U P ac e (Z⟦n⟧) wn
      (P.map ((RX.commShiftIso n).hom.app K) ≫
        (P.commShiftIso n).hom.app (RX.obj K) ≫
          (rF.inv.app K ≫ RY.map (adj.counit.app L))⟦n⟧' ≫
            (RY.commShiftIso n).inv.app L) =
    (RX.commShiftIso n).hom.app K ≫
      (relativeHom I U P ac e Z w
        (rF.inv.app K ≫ RY.map (adj.counit.app L)))⟦n⟧' ≫
      (H.commShiftIso n).inv.app (RY.obj L) ≫
        H.map ((RY.commShiftIso n).inv.app L) at h
  have ha : P.map ((RX.commShiftIso n).hom.app K) ≫
      (P.commShiftIso n).hom.app (RX.obj K) ≫
        (rF.inv.app K ≫ RY.map (adj.counit.app L))⟦n⟧' ≫
          (RY.commShiftIso n).inv.app L =
      rF.inv.app (K⟦n⟧) ≫
        RY.map ((F.commShiftIso n).hom.app K ≫ (adj.counit.app L)⟦n⟧') := by
    have hr := NatTrans.shift_app_comm rF.inv n K
    rw [Functor.commShiftIso_comp_hom_app RX P,
      Functor.commShiftIso_comp_hom_app F RY] at hr
    simp only [Category.assoc] at hr
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hr, ← Functor.commShiftIso_hom_naturality_assoc]
    simp only [Functor.id_obj, Functor.comp_obj, Iso.hom_inv_id_app,
      Category.comp_id]
  have heps : adj.homEquiv (G.obj L) L (adj.counit.app L) = 𝟙 _ :=
    adj.right_triangle_components L
  rw [ha, ← hn (K⟦n⟧) (L⟦n⟧) (Z⟦n⟧) wn _,
    ← hn K L Z w _, adjHom_shift, heps] at h
  erw [(shiftFunctor C n).map_id (G.obj L), Category.id_comp,
    RX.map_id (G.obj L), Category.id_comp] at h
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  exact normalizedCounit_square RX RY G H rG n L h

/-- A normalized relative adjunction transports the specified exceptional shifts.
Only compatibility of the right realization is asserted: the restricted adjunction,
left shifts, left comparison, boundedness and origins are inputs. -/
theorem specifiedExceptionalRealization_shift
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
    (c : Compactification f)
    [(Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).IsLeftAdjoint] :
    letI := (Adjunction.ofIsLeftAdjoint
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} Λ) c)).rightAdjointCommShift ℤ
    letI : (sfFiniteExceptionalAt Λ c).CommShift ℤ :=
      inferInstanceAs (((comparisonLowerStar (ModuleCat.{u + 1} Λ) Y).rightDerivedFunctor ⋙
        (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} Λ) c).rightAdjoint ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory).CommShift ℤ)
    ∀ {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
      [HasShift C ℤ] [HasShift D ℤ]
      (RX : C ⥤ DerivedCategory
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
      (RY : D ⥤ DerivedCategory
        (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
      [RX.Full] [RX.Faithful] [RY.Full] [RY.Faithful]
      [RX.CommShift ℤ] [RY.CommShift ℤ]
      (F : C ⥤ D) (G : D ⥤ C) [F.CommShift ℤ] (adj : F ⊣ G)
      (rF : F ⋙ RY ≅ RX ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c)
      (rG : G ⋙ RX ≅ RY ⋙ sfFiniteExceptionalAt Λ c)
      [rF.hom.CommShift ℤ]
      (hX : ∀ K, DerivedCategory.TStructure.t.plus (RX.obj K))
      (hY : ∀ L, DerivedCategory.TStructure.t.plus (RY.obj L))
      (_origin : ∀ K, Nonempty (FixedEtaleOriginWitness X Λ ⟨RX.obj K, hX K⟩)),
      (∀ K L (W : FixedEtaleOriginWitness X Λ ⟨RX.obj K, hX K⟩) (a : F.obj K ⟶ L),
        RX.map (adj.homEquiv K L a) ≫ rG.hom.app L =
          specifiedExceptionalHomEquiv Λ c ⟨RX.obj K, hX K⟩ W ⟨RY.obj L, hY L⟩
            (rF.inv.app K ≫ RY.map a)) →
      letI := adj.rightAdjointCommShift ℤ
      rG.hom.CommShift ℤ := by
  let etShift := (Adjunction.ofIsLeftAdjoint
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} Λ) c)).rightAdjointCommShift ℤ
  let hShift : (sfFiniteExceptionalAt Λ c).CommShift ℤ :=
    inferInstanceAs (((comparisonLowerStar (ModuleCat.{u + 1} Λ) Y).rightDerivedFunctor ⋙
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} Λ) c).rightAdjoint ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory).CommShift ℤ)
  intro C instC D instD shiftC shiftD RX RY
    fullRX faithfulRX fullRY faithfulRY shiftRX shiftRY F G shiftF adj rF rG
    shiftRF hX hY origin hn
  have hFixed := fixedComparison_shift Λ c
  have hComparison := derivedComparison_shift Λ Y
  have hEtale := (Adjunction.ofIsLeftAdjoint
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} Λ) c)).commShift_of_leftAdjoint ℤ
  refine relativeRealization_shift DerivedCategory.Plus.ι
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c)
    (Adjunction.ofIsLeftAdjoint
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c))
    (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y)
    (fixedCompactSupportComparisonIso Λ c) RX RY F G adj rF rG ?_ ?_
  · intro K
    obtain ⟨W⟩ := origin K
    exact ⟨W.complex, ⟨W.iso⟩⟩
  · intro K L Z w a
    dsimp only [relativeHom]
    rw [Adjunction.comp_homEquiv]
    exact hn K L ⟨Z, w⟩ a

end AlgebraicGeometry.ProEtale
