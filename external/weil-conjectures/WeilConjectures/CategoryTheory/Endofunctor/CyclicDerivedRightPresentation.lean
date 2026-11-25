/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedOffDiagonalPresentation
import WeilConjectures.CategoryTheory.Exact.ExactInputDerivedTransformation
import WeilConjectures.CategoryTheory.KInjectiveExactSquare.KInjectiveExactSquareComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.Abelian.SplitSESBoundaryComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift

/-! # Right-derived transport of cyclic presentations

Source: Stacks Project, Derived Categories, Tags 070I, 070K, 070Y and 0152;
the right-derived companion proof plan in CyclicDerivedHomExactSequence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u v w wF uD vD wD wG

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type uD} [Category.{vD} B] [Abelian B] [HasDerivedCategory.{wD} B]
  (T : A ⥤ B) [T.Additive]
  (h : ∀ K : CochainComplex A ℤ,
    ∃ (I : CochainComplex A ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)

private def cyclicComplexUnit :
    T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ T.rightDerivedFunctorOfQuasiIsoResolutions h :=
  whiskerLeft (T.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso B).inv ≫
    (associator _ _ _).inv ≫
    whiskerRight (T.mapHomotopyCategoryFactors (.up ℤ)).inv DerivedCategory.Qh ≫
    (associator _ _ _).hom ≫
    whiskerLeft (HomotopyCategory.quotient A (.up ℤ))
      (T.rightDerivedFunctorOfQuasiIsoResolutionsUnit h) ≫
    (associator _ _ _).inv ≫
    whiskerRight (DerivedCategory.quotientCompQhIso A).hom
      (T.rightDerivedFunctorOfQuasiIsoResolutions h)

private theorem cyclicComplexUnit_isIso (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso ((cyclicComplexUnit T h).app I) := by
  have := T.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h I
  dsimp [cyclicComplexUnit]
  infer_instance

private theorem cyclicComplexUnit_shift
    [(T.rightDerivedFunctorOfQuasiIsoResolutions h).CommShift ℤ]
    (hη : NatTrans.CommShift (T.rightDerivedFunctorOfQuasiIsoResolutionsUnit h) ℤ) :
    NatTrans.CommShift (cyclicComplexUnit T h) ℤ := by
  have := hη
  dsimp only [cyclicComplexUnit]
  infer_instance

private theorem cyclicDerived_shifts :
    ∃ s : (T.rightDerivedFunctorOfQuasiIsoResolutions h).CommShift ℤ,
      (fun [_s : (T.rightDerivedFunctorOfQuasiIsoResolutions h).CommShift ℤ] ↦
        NatTrans.CommShift (T.rightDerivedFunctorOfQuasiIsoResolutionsUnit h) ℤ) (_s := s) := by
  obtain ⟨s, s', hs, hs', ht, _⟩ :=
    exists_unique_exactInputDerivedTransformation (𝟭 A) T T h h (leftUnitor T).inv
  exact ⟨s, hs⟩

-- The split boundary formula avoids computation of the derived functor on the middle term.
private theorem cyclicSplit_boundary
    [(T.rightDerivedFunctorOfQuasiIsoResolutions h).CommShift ℤ]
    (hη : NatTrans.CommShift (T.rightDerivedFunctorOfQuasiIsoResolutionsUnit h) ℤ)
    (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (σ : ∀ n : ℤ, (S.map (HomologicalComplex.eval A (.up ℤ) n)).Splitting)
    (hT : (S.map (T.mapHomologicalComplex (.up ℤ))).ShortExact) :
    DerivedCategory.triangleOfSESδ hT ≫ ((cyclicComplexUnit T h).app S.X₁)⟦(1 : ℤ)⟧' =
      (cyclicComplexUnit T h).app S.X₃ ≫
        (T.rightDerivedFunctorOfQuasiIsoResolutions h).map
          (DerivedCategory.triangleOfSESδ hS) ≫
        ((T.rightDerivedFunctorOfQuasiIsoResolutions h).commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj S.X₁) := by
  let d := CochainComplex.homOfDegreewiseSplit S σ
  let σT (n : ℤ) : ((S.map (T.mapHomologicalComplex (.up ℤ))).map
      (HomologicalComplex.eval B (.up ℤ) n)).Splitting := (σ n).map T
  have hd : ShiftedHom.map d (T.mapHomologicalComplex (.up ℤ)) =
      CochainComplex.homOfDegreewiseSplit (S.map (T.mapHomologicalComplex (.up ℤ))) σT := by
    ext n
    simp [ShiftedHom.map, d, CochainComplex.cocycleOfDegreewiseSplit, σT,
      Functor.map_comp]
  have := cyclicComplexUnit_shift T h hη
  have hn := ShiftedHom.map_naturality d (cyclicComplexUnit T h)
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at hn
  rw [DerivedCategory.triangleOfSESδ_eq_degreewiseSplit S hS σ,
    DerivedCategory.triangleOfSESδ_eq_degreewiseSplit _ hT σT]
  rw [← hd]
  simpa only [ShiftedHom.comp_map, ShiftedHom.map, Functor.comp_obj,
    Functor.comp_map, commShiftIso_comp_hom_app, Functor.map_comp, Category.assoc, d,
    ShortComplex.map_X₁, ShortComplex.map_X₃] using hn

end CategoryTheory.Functor

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (G : D ⥤ D) [G.Additive] [G.IsEquivalence]
  [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wG} (IsoAlgebra G)]
  (L : C ⥤ D) [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{vD} D]
  [PreservesFiniteLimits L]
  (hF : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
    ∃ (I : CochainComplex (IsoAlgebra F) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
  (hC : ∀ K : CochainComplex C ℤ,
    ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
  [(L.rightDerivedFunctorOfQuasiIsoResolutions hC).CommShift ℤ]
  (hσ : NatTrans.CommShift (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC) ℤ)

include hσ in
private theorem rightComparison_shifts
    [((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF).CommShift ℤ]
    (hη : NatTrans.CommShift
      ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutionsUnit hF) ℤ) :
    NatTrans.CommShift (cyclicDerivedRightForgetComparison F G L e hF hC).hom ℤ := by
  have := hη
  have := hσ
  have : IsGrothendieckAbelian.{v} (IsoAlgebra F) := isGrothendieckAbelian F
  let c := KInjectiveExactSquare.sourceIso (mapOfNatIso e) L (forget F) (forget G) rfl
  -- These associators also specify the composite functors' coherent shift structures.
  let a : (forget F).mapHomotopyCategory (.up ℤ) ⋙
      L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙
        ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF ⋙
          (forget G).mapDerivedCategory) :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight c.hom DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ((mapOfNatIso e).mapHomotopyCategory (.up ℤ))
        (forget G).mapDerivedCategoryFactorsh.inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutionsUnit hF)
        (forget G).mapDerivedCategory ≫
      (Functor.associator _ _ _).hom
  let b : (forget F).mapHomotopyCategory (.up ℤ) ⋙
      L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙
        ((forget F).mapDerivedCategory ⋙ L.rightDerivedFunctorOfQuasiIsoResolutions hC) :=
    Functor.whiskerLeft ((forget F).mapHomotopyCategory (.up ℤ))
        (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (forget F).mapDerivedCategoryFactorsh.inv
        (L.rightDerivedFunctorOfQuasiIsoResolutions hC) ≫
      (Functor.associator _ _ _).hom
  let hcshift : NatTrans.CommShift c.hom ℤ := by
    dsimp only [c, KInjectiveExactSquare.sourceIso, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have ha : NatTrans.CommShift a ℤ := by
    dsimp only [a]
    infer_instance
  have hb : NatTrans.CommShift b ℤ := by
    dsimp only [b]
    infer_instance
  let α := cyclicDerivedRightForgetComparison F G L e hF hC
  have hab : a ≫ Functor.whiskerLeft DerivedCategory.Qh α.hom = b := by
    ext K
    have he := (Classical.choose_spec
      (exists_fixedPairDerivedForgetComparison F G L e hF hC)).1 K
    have hc : DerivedCategory.Qh.map (c.inv.app K) =
        DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (mapOfNatIsoCompForgetIso e)
              (.up ℤ)).hom.app K) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (forget F ⋙ L))
              (.up ℤ)).inv.app K) := by
      rw [← Functor.map_comp]
      rfl
    rw [← reassoc_of% hc] at he
    apply (cancel_epi ((forget G).mapDerivedCategoryFactorsh.hom.app
      (((mapOfNatIso e).mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map (c.inv.app K))).mp
    apply (cancel_mono ((L.rightDerivedFunctorOfQuasiIsoResolutions hC).map
      ((forget F).mapDerivedCategoryFactorsh.hom.app K))).mp
    simp only [a, b, α, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.assoc, Category.id_comp,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
    simp only [← Functor.map_comp, Iso.inv_hom_id_app]
    erw [Functor.map_id, Category.comp_id]
    exact he
  have hi : IsIso (Functor.whiskerLeft
      (ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic
        (IsoAlgebra F)).rightOrthogonal) a) := by
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun X ↦ by
      obtain ⟨I, hI, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
      have := hI
      have := (mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso hF I
      change IsIso (a.app ((HomotopyCategory.quotient _ _).obj I))
      dsimp only [a, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
      infer_instance)
  have : NatTrans.CommShift (a ≫ Functor.whiskerLeft DerivedCategory.Qh α.hom) ℤ := by
    rw [hab]
    exact hb
  exact NatTrans.CommShift.of_comp_whiskerLeft_Qh a α.hom

omit [(L.rightDerivedFunctorOfQuasiIsoResolutions hC).CommShift ℤ] in
private theorem rightComparison_unit (K : CochainComplex (IsoAlgebra F) ℤ) :
    (forget G).mapDerivedCategory.map
        ((Functor.cyclicComplexUnit (mapOfNatIso e) hF).app K) ≫
      (cyclicDerivedRightForgetComparison F G L e hF hC).hom.app (DerivedCategory.Q.obj K) ≫
      (L.rightDerivedFunctorOfQuasiIsoResolutions hC).map
        ((forget F).mapDerivedCategoryFactors.hom.app K) =
    (forget G).mapDerivedCategoryFactors.hom.app
        (((mapOfNatIso e).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (Functor.cyclicComplexUnit L hC).app
        (((forget F).mapHomologicalComplex (.up ℤ)).obj K) := by
  have ht := (Classical.choose_spec
    (exists_fixedPairDerivedForgetComparison F G L e hF hC)).1
      ((HomotopyCategory.quotient _ _).obj K)
  change (forget G).mapDerivedCategory.map
      (((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutionsUnit hF).app
        ((HomotopyCategory.quotient _ _).obj K)) ≫
      (cyclicDerivedRightForgetComparison F G L e hF hC).hom.app _ ≫
      (L.rightDerivedFunctorOfQuasiIsoResolutions hC).map
        ((forget F).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient _ _).obj K)) =
    (forget G).mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ _).obj
          (((mapOfNatIso e).mapHomologicalComplex (.up ℤ)).obj K)) ≫
      DerivedCategory.Qh.map (𝟙 _) ≫ DerivedCategory.Qh.map (𝟙 _) ≫
      (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC).app
        ((HomotopyCategory.quotient _ _).obj
          (((forget F).mapHomologicalComplex (.up ℤ)).obj K)) at ht
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app, Functor.map_id,
    Category.id_comp] at ht
  -- `quotientCompQhIso` is no longer a definitional identity: conjugate by it.
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv, Functor.map_comp,
    Category.assoc] at ht
  have hn := (cyclicDerivedRightForgetComparison F G L e hF hC).hom.naturality
    ((DerivedCategory.quotientCompQhIso (IsoAlgebra F)).hom.app K)
  simp only [Functor.comp_map] at hn
  dsimp only [Functor.cyclicComplexUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv, Functor.map_id,
    Functor.map_comp, Category.id_comp, Category.assoc]
  rw [reassoc_of% hn]
  dsimp only [Functor.comp_obj] at ht ⊢
  simp only [Functor.map_id, Category.id_comp, Category.comp_id] at ht ⊢
  rw [← cancel_epi ((forget G).mapDerivedCategory.map
      ((DerivedCategory.quotientCompQhIso (IsoAlgebra G)).hom.app _)),
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
  rw [← cancel_mono ((L.rightDerivedFunctorOfQuasiIsoResolutions hC).map
      ((DerivedCategory.quotientCompQhIso C).inv.app _))]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at ht ⊢
  dsimp only [Functor.comp_obj]
  simp only [Functor.map_id, Category.comp_id]
  exact ht

private def rightFactors (K : CochainComplex (IsoAlgebra F) ℤ) [K.IsKInjective] :
    ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF).obj
        (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (((mapOfNatIso e).mapHomologicalComplex (.up ℤ)).obj K) :=
  have := Functor.cyclicComplexUnit_isIso (mapOfNatIso e) hF K
  (asIso ((Functor.cyclicComplexUnit (mapOfNatIso e) hF).app K)).symm

private def underlyingFactors (K : CochainComplex C ℤ) [K.IsKInjective] :
    (L.rightDerivedFunctorOfQuasiIsoResolutions hC).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj K) :=
  have := Functor.cyclicComplexUnit_isIso L hC K
  (asIso ((Functor.cyclicComplexUnit L hC).app K)).symm

omit [(L.rightDerivedFunctorOfQuasiIsoResolutions hC).CommShift ℤ] in
private theorem rightComparison_factors (K : CochainComplex (IsoAlgebra F) ℤ)
    [K.IsKInjective] :
    (cyclicDerivedRightForgetComparison F G L e hF hC).hom.app (DerivedCategory.Q.obj K) ≫
        (L.rightDerivedFunctorOfQuasiIsoResolutions hC).map
          ((forget F).mapDerivedCategoryFactors.hom.app K) ≫
        (underlyingFactors L hC
          (((forget F).mapHomologicalComplex (.up ℤ)).obj K)).hom =
      (forget G).mapDerivedCategory.map ((rightFactors F G L e hF K).hom) ≫
        (forget G).mapDerivedCategoryFactors.hom.app
          (((mapOfNatIso e).mapHomologicalComplex (.up ℤ)).obj K) := by
  have := Functor.cyclicComplexUnit_isIso (mapOfNatIso e) hF K
  have := Functor.cyclicComplexUnit_isIso L hC
    (((forget F).mapHomologicalComplex (.up ℤ)).obj K)
  apply (cancel_epi ((forget G).mapDerivedCategory.map
    ((Functor.cyclicComplexUnit (mapOfNatIso e) hF).app K))).mp
  simp only [← Category.assoc, rightComparison_unit F G L e hF hC K]
  simp only [rightFactors, underlyingFactors, Iso.symm_hom, asIso_inv]
  rw [← Functor.map_comp, IsIso.hom_inv_id, Functor.map_id, Category.id_comp]
  simp

omit [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{vD} D]
  [PreservesFiniteLimits L] [(L.rightDerivedFunctorOfQuasiIsoResolutions hC).CommShift ℤ] in
private theorem underlyingFactors_natural {A B : CochainComplex C ℤ}
    [A.IsKInjective] [B.IsKInjective] (z : B ⟶ A) :
    (L.rightDerivedFunctorOfQuasiIsoResolutions hC).map (DerivedCategory.Q.map z) ≫
        (underlyingFactors L hC A).hom =
      (underlyingFactors L hC B).hom ≫
        DerivedCategory.Q.map ((L.mapHomologicalComplex (.up ℤ)).map z) := by
  have := Functor.cyclicComplexUnit_isIso L hC A
  have := Functor.cyclicComplexUnit_isIso L hC B
  apply (cancel_epi ((Functor.cyclicComplexUnit L hC).app B)).mp
  rw [← Category.assoc]
  erw [← (Functor.cyclicComplexUnit L hC).naturality z]
  simp [underlyingFactors, Category.assoc]

include hσ in
private theorem rightComparison_shift
    [((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF).CommShift ℤ]
    (hη : NatTrans.CommShift
      ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutionsUnit hF) ℤ)
    (X : DerivedCategory (IsoAlgebra F)) :
    let U := (forget F).mapDerivedCategory
    let V := (forget G).mapDerivedCategory
    let J := ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF)
    let H := (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
    let α := cyclicDerivedRightForgetComparison F G L e hF hC
    α.hom.app X ≫ H.map (U.map
        ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).inv.app X)) ≫
      H.map ((U.commShiftIso (-1 : ℤ)).hom.app (X⟦(1 : ℤ)⟧)) ≫
      (H.commShiftIso (-1 : ℤ)).hom.app (U.obj (X⟦(1 : ℤ)⟧)) =
    V.map ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).inv.app (J.obj X)) ≫
      (V.commShiftIso (-1 : ℤ)).hom.app ((J.obj X)⟦(1 : ℤ)⟧) ≫
      (V.map ((J.commShiftIso (1 : ℤ)).inv.app X))⟦(-1 : ℤ)⟧' ≫
      (α.hom.app (X⟦(1 : ℤ)⟧))⟦(-1 : ℤ)⟧' := by
  dsimp only
  let α := cyclicDerivedRightForgetComparison F G L e hF hC
  have : NatTrans.CommShift α.hom ℤ := by
    exact rightComparison_shifts F G L e hF hC hσ hη
  have h := NatTrans.shift_app_comm α.hom (-1 : ℤ) (X⟦(1 : ℤ)⟧)
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
    Category.assoc] at h
  rw [← Functor.comp_map, ← α.hom.naturality_assoc]
  dsimp only [Functor.comp_map, Functor.comp_obj]
  rw [← h, Functor.map_shiftFunctorCompIsoId_inv_app]
  simp [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc,
    ← Functor.commShiftIso_hom_naturality_assoc]
  rfl

omit [(L.rightDerivedFunctorOfQuasiIsoResolutions hC).CommShift ℤ] in
private theorem rightComparison_core
    {A B : CochainComplex (IsoAlgebra F) ℤ} [A.IsKInjective] [B.IsKInjective]
    (z : ((forget F).mapHomologicalComplex (.up ℤ)).obj B ⟶
      ((forget F).mapHomologicalComplex (.up ℤ)).obj A) :
    let V := (forget G).mapDerivedCategory
    let H := (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
    let α := cyclicDerivedRightForgetComparison F G L e hF hC
    α.hom.app (DerivedCategory.Q.obj B) ≫
      H.map ((forget F).mapDerivedCategoryFactors.hom.app B ≫ DerivedCategory.Q.map z ≫
        (forget F).mapDerivedCategoryFactors.inv.app A) =
      V.map ((rightFactors F G L e hF B).hom) ≫
        (forget G).mapDerivedCategoryFactors.hom.app
          (((mapOfNatIso e).mapHomologicalComplex (.up ℤ)).obj B) ≫
        DerivedCategory.Q.map ((L.mapHomologicalComplex (.up ℤ)).map z) ≫
        (forget G).mapDerivedCategoryFactors.inv.app
          (((mapOfNatIso e).mapHomologicalComplex (.up ℤ)).obj A) ≫
        V.map ((rightFactors F G L e hF A).inv) ≫
        α.hom.app (DerivedCategory.Q.obj A) := by
  dsimp only
  apply (cancel_mono ((L.rightDerivedFunctorOfQuasiIsoResolutions hC).map
    ((forget F).mapDerivedCategoryFactors.hom.app A) ≫
      (underlyingFactors L hC
        (((forget F).mapHomologicalComplex (.up ℤ)).obj A)).hom)).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [rightComparison_factors F G L e hF hC A]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Iso.inv_hom_id]
  erw [Category.comp_id, Functor.map_id, Category.id_comp, Iso.inv_hom_id_app,
    Category.comp_id]
  rw [Functor.map_comp, Category.assoc, underlyingFactors_natural L hC]
  simpa only [Category.assoc] using
    congrArg (fun t ↦ t ≫ DerivedCategory.Q.map
      ((L.mapHomologicalComplex (.up ℤ)).map z)) (rightComparison_factors F G L e hF hC B)

private theorem rightTransport_endpoints
    {M N M' N' : DerivedCategory (IsoAlgebra F)} (a : M ⟶ M') (c : N' ⟶ N)
    (z : CyclicDerivedHom F M' N' (-1)) :
    let U := (forget F).mapDerivedCategory
    let V := (forget G).mapDerivedCategory
    let J := ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF)
    let H := (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
    let α := cyclicDerivedRightForgetComparison F G L e hF hC
    cyclicDerivedHomTransport F G J H (fun r ↦ H.commShiftIso r) α M N (-1)
      (U.map a ≫ z ≫ (U.map c)⟦(-1 : ℤ)⟧') =
      V.map (J.map a) ≫
        cyclicDerivedHomTransport F G J H (fun r ↦ H.commShiftIso r) α M' N' (-1) z ≫
        (V.map (J.map c))⟦(-1 : ℤ)⟧' := by
  dsimp only
  let α := cyclicDerivedRightForgetComparison F G L e hF hC
  have ha := α.hom.naturality a
  have hc := α.inv.naturality c
  simp only [Functor.comp_map, Functor.comp_obj] at ha hc
  dsimp only [α] at ha hc
  dsimp only [cyclicDerivedHomTransport]
  simp only [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality_assoc]
  rw [← reassoc_of% ha]
  rw [← (shiftFunctor (DerivedCategory D) (-1 : ℤ)).map_comp, hc]
  simp only [Functor.map_comp]

omit [IsGrothendieckAbelian.{vD} D] in
private theorem cancellation_natural
    {X Y : DerivedCategory (IsoAlgebra G)} (b : X ⟶ Y) :
    let V := (forget G).mapDerivedCategory
    let η := shiftFunctorCompIsoId (DerivedCategory (IsoAlgebra G)) (1 : ℤ) (-1) (by omega)
    V.map b ≫ V.map (η.inv.app Y) ≫
        (V.commShiftIso (-1 : ℤ)).hom.app (Y⟦(1 : ℤ)⟧) =
      V.map (η.inv.app X) ≫ (V.commShiftIso (-1 : ℤ)).hom.app (X⟦(1 : ℤ)⟧) ≫
        (V.map (b⟦(1 : ℤ)⟧'))⟦(-1 : ℤ)⟧' := by
  dsimp only
  let η := shiftFunctorCompIsoId (DerivedCategory (IsoAlgebra G)) (1 : ℤ) (-1) (by omega)
  have h := η.inv.naturality b
  change b ≫ η.inv.app Y = η.inv.app X ≫ b⟦(1 : ℤ)⟧'⟦(-1 : ℤ)⟧' at h
  rw [← Functor.map_comp_assoc, h, Functor.map_comp]
  simp only [Category.assoc, Functor.commShiftIso_hom_naturality]
  rfl

include hσ in
private theorem rightTransport_class
    [((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF).CommShift ℤ]
    (hη : NatTrans.CommShift
      ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutionsUnit hF) ℤ)
    {S : ShortComplex (CochainComplex (IsoAlgebra F) ℤ)}
    [S.X₁.IsKInjective] [S.X₃.IsKInjective]
    (z : ((forget F).mapHomologicalComplex (.up ℤ)).obj S.X₃ ⟶
      ((forget F).mapHomologicalComplex (.up ℤ)).obj S.X₁) :
    let V := (forget G).mapDerivedCategory
    let J := ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF)
    let Jc := (mapOfNatIso e).mapHomologicalComplex (.up ℤ)
    let H := (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
    let α := cyclicDerivedRightForgetComparison F G L e hF hC
    cyclicDerivedHomTransport F G J H (fun r ↦ H.commShiftIso r) α
        (DerivedCategory.Q.obj S.X₃) ((DerivedCategory.Q.obj S.X₁)⟦(1 : ℤ)⟧) (-1)
        (cyclicDerivedOffDiagonalClass F z) =
      V.map ((rightFactors F G L e hF S.X₃).hom) ≫
        cyclicDerivedOffDiagonalClass G (S := S.map Jc)
          ((L.mapHomologicalComplex (.up ℤ)).map z) ≫
        (V.map (((rightFactors F G L e hF S.X₁).inv)⟦(1 : ℤ)⟧' ≫
          (J.commShiftIso (1 : ℤ)).inv.app (DerivedCategory.Q.obj S.X₁)))⟦(-1 : ℤ)⟧' := by
  dsimp only
  let U := (forget F).mapDerivedCategory
  let V := (forget G).mapDerivedCategory
  let J := ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF)
  let H := (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
  let α := cyclicDerivedRightForgetComparison F G L e hF hC
  let X := DerivedCategory.Q.obj S.X₁
  let η := shiftFunctorCompIsoId (DerivedCategory (IsoAlgebra F)) (1 : ℤ) (-1) (by omega)
  let core := (forget F).mapDerivedCategoryFactors.hom.app S.X₃ ≫
    DerivedCategory.Q.map z ≫ (forget F).mapDerivedCategoryFactors.inv.app S.X₁
  calc
    _ = (α.hom.app (DerivedCategory.Q.obj S.X₃) ≫ H.map core) ≫
        H.map (U.map (η.inv.app X)) ≫ H.map ((U.commShiftIso (-1 : ℤ)).hom.app
          (X⟦(1 : ℤ)⟧)) ≫ (H.commShiftIso (-1 : ℤ)).hom.app (U.obj (X⟦(1 : ℤ)⟧)) ≫
          (α.inv.app (X⟦(1 : ℤ)⟧))⟦(-1 : ℤ)⟧' := by
      simp only [cyclicDerivedHomTransport, cyclicDerivedOffDiagonalClass, core,
        Functor.map_comp, Category.assoc]
      rfl
    _ = _ := by
      rw [rightComparison_core F G L e hF hC z]
      simp only [Category.assoc]
      rw [reassoc_of% (rightComparison_shift F G L e hF hC hσ hη X)]
      have hα := ((shiftFunctor (DerivedCategory D) (-1 : ℤ)).mapIso
        (α.app (X⟦(1 : ℤ)⟧))).hom_inv_id
      change (α.hom.app (X⟦(1 : ℤ)⟧))⟦(-1 : ℤ)⟧' ≫
        (α.inv.app (X⟦(1 : ℤ)⟧))⟦(-1 : ℤ)⟧' = 𝟙 _ at hα
      rw [hα]
      erw [Category.comp_id]
      rw [reassoc_of% (cancellation_natural G
        ((rightFactors F G L e hF S.X₁).inv))]
      simp only [cyclicDerivedOffDiagonalClass, Functor.map_comp, Category.assoc]
      rfl

private structure InjectivePresentation
    (M N : DerivedCategory (IsoAlgebra F)) (u : CyclicDerivedHom F M N (-1))
    (f : M ⟶ N) where
  S : ShortComplex (CochainComplex (IsoAlgebra F) ℤ)
  shortExact : S.ShortExact
  u₀ : ((forget F).mapHomologicalComplex (.up ℤ)).obj S.X₃ ⟶
    ((forget F).mapHomologicalComplex (.up ℤ)).obj S.X₁
  s : ((forget F).mapHomologicalComplex (.up ℤ)).obj S.X₃ ⟶
    ((forget F).mapHomologicalComplex (.up ℤ)).obj S.X₂
  a : M ≅ DerivedCategory.Q.obj S.X₃
  c : (DerivedCategory.Q.obj S.X₁)⟦(1 : ℤ)⟧ ≅ N
  hA : S.X₁.IsKInjective
  hJ : S.X₃.IsKInjective
  injective : ∀ n : ℤ, Injective (S.X₁.X n)
  hs : s ≫ ((forget F).mapHomologicalComplex (.up ℤ)).map S.g = 𝟙 _
  he : ∀ n : ℤ,
    F.map (@id ((S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier) (s.f n)) ≫
        (S.X₂.X n).str.hom =
      ((S.X₃.X n).str.hom ≫
        @id ((S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier) (s.f n)) +
      (F.map (@id ((S.X₃.X n).carrier ⟶ (S.X₁.X n).carrier) (u₀.f n)) ≫
        (S.X₁.X n).str.hom ≫
          @id ((S.X₁.X n).carrier ⟶ (S.X₂.X n).carrier) ((forget F).map (S.f.f n)))
  hu : u = (forget F).mapDerivedCategory.map a.hom ≫ cyclicDerivedOffDiagonalClass F u₀ ≫
    ((forget F).mapDerivedCategory.map c.hom)⟦(-1 : ℤ)⟧'
  hf : f = a.hom ≫ DerivedCategory.triangleOfSESδ shortExact ≫ c.hom

private theorem exists_injectivePresentation
    {M N : DerivedCategory (IsoAlgebra F)} {u : CyclicDerivedHom F M N (-1)}
    {f : M ⟶ N} (hgiven : CyclicDerivedOffDiagonalPresentation F u f) :
    Nonempty (InjectivePresentation F M N u f) := by
  have : IsGrothendieckAbelian.{v} (IsoAlgebra F) := isGrothendieckAbelian F
  let KM := DerivedCategory.Q.objPreimage M
  let KN := DerivedCategory.Q.objPreimage (N⟦(-1 : ℤ)⟧)
  let J := (CochainComplex.kInjectiveResolutionFunctor (IsoAlgebra F)).obj KM
  let A := (CochainComplex.kInjectiveResolutionFunctor (IsoAlgebra F)).obj KN
  let sJ := (CochainComplex.toKInjectiveResolution (IsoAlgebra F)).app KM
  let sA := (CochainComplex.toKInjectiveResolution (IsoAlgebra F)).app KN
  have hJ : J.IsKInjective := inferInstance
  have hA : A.IsKInjective := inferInstance
  have hsJ : QuasiIso sJ :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ KM).2
  have hsA : QuasiIso sA :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ KN).2
  have := hJ
  have := hA
  have := hsJ
  have := hsA
  let U := (forget F).mapDerivedCategory
  let Uc := (forget F).mapHomologicalComplex (.up ℤ)
  let a : M ≅ DerivedCategory.Q.obj J :=
    (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫ asIso (DerivedCategory.Q.map sJ)
  let c : (DerivedCategory.Q.obj A)⟦(1 : ℤ)⟧ ≅ N :=
    (shiftFunctor _ (1 : ℤ)).mapIso
      ((asIso (DerivedCategory.Q.map sA)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso _) ≪≫
      (shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by omega)).app N
  let k : U.obj (DerivedCategory.Q.obj A) ≅
      (U.obj ((DerivedCategory.Q.obj A)⟦(1 : ℤ)⟧))⟦(-1 : ℤ)⟧ :=
    U.mapIso ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).symm.app
      (DerivedCategory.Q.obj A)) ≪≫
        (U.commShiftIso (-1 : ℤ)).app ((DerivedCategory.Q.obj A)⟦(1 : ℤ)⟧)
  let a' : U.obj M ≅ DerivedCategory.Q.obj (Uc.obj J) :=
    U.mapIso a ≪≫ (forget F).mapDerivedCategoryFactors.app J
  let c' : DerivedCategory.Q.obj (Uc.obj A) ≅ (U.obj N)⟦(-1 : ℤ)⟧ :=
    ((forget F).mapDerivedCategoryFactors.app A).symm ≪≫ k ≪≫
      (shiftFunctor _ (-1 : ℤ)).mapIso (U.mapIso c)
  have : CochainComplex.IsKInjective (Uc.obj A) := inferInstance
  obtain ⟨u₀, hu₀⟩ := CochainComplex.IsKInjective.exists_Q_map_eq (Uc.obj J) (Uc.obj A)
    (a'.inv ≫ u ≫ c'.inv)
  obtain ⟨E, f, g, w, hS, s, hs, he⟩ := exists_cyclicDerivedStrictExtension F A J u₀
  have hu : u = U.map a.hom ≫ cyclicDerivedOffDiagonalClass F (S := ShortComplex.mk f g w) u₀ ≫
      (U.map c.hom)⟦(-1 : ℤ)⟧' := by
    dsimp [cyclicDerivedOffDiagonalClass]
    rw [hu₀]
    simp [a', c', k, U, Category.assoc]
  have hp : CyclicDerivedOffDiagonalPresentation F u
      (a.hom ≫ DerivedCategory.triangleOfSESδ hS ≫ c.hom) := by
    exact ⟨ShortComplex.mk f g w, hS, u₀, s, a, c, hs, he, hu, rfl⟩
  exact ⟨ShortComplex.mk f g w, hS, u₀, s, a, c, hA, hJ,
    (fun n ↦ inferInstance), hs, he, hu,
    (cyclicDerivedOffDiagonalPresentation_unique F hp hgiven).symm⟩

include hσ in
/-- Right derivation preserves a strict cyclic presentation after replacing its models.

Proof: replace M and N[-1] by K-injective complexes with injective terms, and represent
the underlying morphism by a chain map, using exact forgetting and the K-injective Hom
bijection. Form its triangular extension A → E → J. Since A has injective terms, the
sequence splits in each degree in the fixed-pair category. Hence E and the cone of the
inclusion are K-injective: the degreewise split sequence gives a distinguished homotopy
triangle, and K-injectives form a triangulated subcategory. The cone projection to J is
a quasi-isomorphism between K-injectives, hence a homotopy equivalence. The uniqueness
of strict presentations identifies the original native morphism with this extension's
connecting morphism. Compute the right derived equivariant functor by its unit on these
models. Additivity preserves the degreewise splitting, cones and the homotopy inverse.
Thus the canonical signed formula for the SES connecting morphism, minus the cone
projection inverse followed by the shifted inclusion projection, is preserved. The
unit-normalized forgetting comparison and hσ identify the transported underlying class.
Naturality of e makes the image upper action entry exactly the target diagonal action
composed with P' of the image chain map. The image sequence, splitting, chain map and
endpoint isomorphisms therefore give the required strict presentation. This argument
uses no boundedness of either endpoint and no normalization predicate on a boundary.

Source: the K-injective and cone steps of the parent right-derived companion; Stacks
derived.tex, Tags 070I, 070K, 070Y and 0152, and injectives.tex, Tag 079P.
(blueprint: lem-sf-cyclic-derived-right-presentation). -/
theorem cyclicDerivedOffDiagonalPresentation_mapRightDerived
    {M N : DerivedCategory (IsoAlgebra F)} {u : CyclicDerivedHom F M N (-1)}
    {f : M ⟶ N} (hp : CyclicDerivedOffDiagonalPresentation F u f) :
    CyclicDerivedOffDiagonalPresentation G
      (cyclicDerivedHomTransport F G
        ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF)
        (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
        (fun r ↦ (L.rightDerivedFunctorOfQuasiIsoResolutions hC).commShiftIso r)
        (cyclicDerivedRightForgetComparison F G L e hF hC) M N (-1) u)
      (((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF).map f) := by
  obtain ⟨sP, hηP⟩ := Functor.cyclicDerived_shifts (mapOfNatIso e) hF
  let := sP
  have := hηP
  obtain ⟨p⟩ := exists_injectivePresentation F hp
  have := p.hA
  have := p.hJ
  let S := p.S
  let J := (mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF
  let Jc := (mapOfNatIso e).mapHomologicalComplex (.up ℤ)
  let Lc := L.mapHomologicalComplex (.up ℤ)
  -- Only the left endpoint needs injective terms; no middle-term resolution is needed.
  let σ (n : ℤ) : (S.map (HomologicalComplex.eval (IsoAlgebra F) (.up ℤ) n)).Splitting := by
    have : Injective ((S.map
        (HomologicalComplex.eval (IsoAlgebra F) (.up ℤ) n)).X₁) := p.injective n
    exact ShortComplex.ShortExact.splittingOfInjective
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp p.shortExact n)
  have hT : (S.map Jc).ShortExact := by
    rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
    intro n
    exact ((σ n).map (mapOfNatIso e)).shortExact
  let a' := J.mapIso p.a ≪≫ rightFactors F G L e hF S.X₃
  let c' := (shiftFunctor _ (1 : ℤ)).mapIso (rightFactors F G L e hF S.X₁).symm ≪≫
    (J.commShiftIso (1 : ℤ)).symm.app (DerivedCategory.Q.obj S.X₁) ≪≫ J.mapIso p.c
  refine ⟨S.map Jc, hT, Lc.map p.u₀, Lc.map p.s, a', c', ?_, ?_, ?_, ?_⟩
  · change Lc.map p.s ≫ Lc.map (((forget F).mapHomologicalComplex (.up ℤ)).map S.g) = 𝟙 _
    rw [← Lc.map_comp, p.hs, Lc.map_id]
  · intro n
    let en (X : C) : G.obj (L.obj X) ⟶ L.obj (F.obj X) := e.hom.app X
    let sn : (S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier := p.s.f n
    let un : (S.X₃.X n).carrier ⟶ (S.X₁.X n).carrier := p.u₀.f n
    let jn : (S.X₁.X n).carrier ⟶ (S.X₂.X n).carrier := (forget F).map (S.f.f n)
    change G.map (L.map sn) ≫
        (en (S.X₂.X n).carrier ≫ L.map (S.X₂.X n).str.hom) =
      (en (S.X₃.X n).carrier ≫ L.map (S.X₃.X n).str.hom) ≫ L.map sn +
        G.map (L.map un) ≫ (en (S.X₁.X n).carrier ≫
          L.map (S.X₁.X n).str.hom) ≫ L.map jn
    have h := congrArg L.map (p.he n)
    change L.map (F.map sn ≫ (S.X₂.X n).str.hom) =
      L.map ((S.X₃.X n).str.hom ≫ sn +
        F.map un ≫ (S.X₁.X n).str.hom ≫ jn) at h
    simp only [Functor.map_comp, Functor.map_add] at h
    have hn := e.hom.naturality sn
    have hn' := e.hom.naturality un
    change G.map (L.map sn) ≫ en (S.X₂.X n).carrier =
      en (S.X₃.X n).carrier ≫ L.map (F.map sn) at hn
    change G.map (L.map un) ≫ en (S.X₁.X n).carrier =
      en (S.X₃.X n).carrier ≫ L.map (F.map un) at hn'
    simp only [← Category.assoc]
    rw [hn, hn']
    simpa only [Category.assoc, Preadditive.comp_add] using
      congrArg (fun t ↦ en (S.X₃.X n).carrier ≫ t) h
  · simp only [p.hu]
    rw [rightTransport_endpoints F G L e hF hC p.a.hom p.c.hom,
      rightTransport_class F G L e hF hC hσ hηP p.u₀]
    simp only [a', c', Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Functor.map_comp, Category.assoc]
    rfl
  · have hb := Functor.cyclicSplit_boundary (mapOfNatIso e) hF hηP S p.shortExact σ hT
    have hA := Functor.cyclicComplexUnit_isIso (mapOfNatIso e) hF S.X₁
    have hJ := Functor.cyclicComplexUnit_isIso (mapOfNatIso e) hF S.X₃
    have hd : J.map (DerivedCategory.triangleOfSESδ p.shortExact) =
        (rightFactors F G L e hF S.X₃).hom ≫ DerivedCategory.triangleOfSESδ hT ≫
          (rightFactors F G L e hF S.X₁).inv⟦(1 : ℤ)⟧' ≫
          (J.commShiftIso (1 : ℤ)).inv.app (DerivedCategory.Q.obj S.X₁) := by
      apply (cancel_epi ((Functor.cyclicComplexUnit (mapOfNatIso e) hF).app S.X₃)).mp
      simp only [rightFactors, Iso.symm_hom, Iso.symm_inv, asIso_hom, asIso_inv]
      erw [IsIso.hom_inv_id_assoc]
      rw [reassoc_of% hb]
      simp only [J, Iso.hom_inv_id_app]
      erw [Category.comp_id]
    rw [p.hf, Functor.map_comp, Functor.map_comp, hd]
    simp only [a', c', Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
    rfl

end CategoryTheory.Endofunctor.IsoAlgebra
