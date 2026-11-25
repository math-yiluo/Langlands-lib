/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedFreeHomCoordinates
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # The free cyclic differential in adjunction coordinates

Source: Stacks Tags 0149, 0152, and the normalized cyclic free resolution.
(blueprint: lem-sf-cyclic-free-defect-coordinates).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w wF

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence] [IsGrothendieckAbelian.{v} C]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]

-- The summand-one calculation avoids choosing an inverse cyclic action.
omit [F.Additive] [HasDerivedCategory.{w} C]
    [HasDerivedCategory.{wF} (IsoAlgebra F)] in
private lemma heart_unit (M : C) :
    (Free.adjunction F).unit.app M = Sigma.ι (Free.obj F M) 0 := by
  change Sigma.ι _ 0 ≫ 𝟙 _ = _
  exact Category.comp_id _

private lemma heart_difference (R : CyclicDerivedFreeResolution F) (M : IsoAlgebra F) :
    F.map ((Free.adjunction F).unit.app M.carrier) ≫ (Free.str F M.carrier).hom ≫
        (forget F).map (R.d.app M) =
      @HSub.hSub (F.obj M.carrier ⟶ ∐ Free.obj F M.carrier)
        (F.obj M.carrier ⟶ ∐ Free.obj F M.carrier)
        (F.obj M.carrier ⟶ ∐ Free.obj F M.carrier) inferInstance
        (F.map ((Free.adjunction F).unit.app M.carrier) ≫ (Free.str F M.carrier).hom)
        (M.str.hom ≫ Sigma.ι (Free.obj F M.carrier) 0) := by
  have ht0 : (R.theta M 0).hom = 𝟙 M.carrier := R.theta_eq M 0
  have ht1 : (R.theta M 1).hom = M.str.hom := by
    rw [R.theta_eq]
    change F.map (𝟙 M.carrier) ≫ M.str.hom = _
    rw [F.map_id, Category.id_comp]
  have ht0i : (R.theta M 0).inv = 𝟙 M.carrier := by
    apply (cancel_mono (R.theta M 0).hom).1
    rw [Iso.inv_hom_id, Category.id_comp, ht0]
  rw [heart_unit, ← Category.assoc, Free.map_ι_comp_str]
  simp only [Free.objSucc, Iso.refl_hom]
  erw [Category.id_comp]
  change Sigma.ι (Free.obj F M.carrier) 1 ≫ (forget F).map (R.d.app M) = _
  have h := R.summand M 1
  erw [show (1 : ℤ) - 1 = 0 by decide, Iso.trans_hom, Iso.symm_hom, ht1, ht0i,
    Category.comp_id] at h
  exact h

omit [IsGrothendieckAbelian.{v} C] in
private lemma structure_fac (K : CochainComplex (IsoAlgebra F) ℤ) :
    (cyclicDerivedStructure F).hom.app (DerivedCategory.Q.obj K) ≫
        (forget F).mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategory.map ((forget F).mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app
          (((forget F).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (strNatIso F).hom (.up ℤ)).app K) := by
  have h := Functor.mapDerivedCategoryNatIso_fac (strNatIso F) K
  have hc := Functor.mapDerivedCategoryCompIso_fac (forget F) F K
  have hid : (Functor.mapHomologicalComplexCompIso (Iso.refl (forget F ⋙ F))
      (.up ℤ)).hom.app K = 𝟙 _ := rfl
  erw [hid, Functor.map_id, Category.comp_id] at hc
  dsimp only [cyclicDerivedStructure, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  erw [Category.assoc, h, ← hc]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

private lemma unit_fac (K : CochainComplex C ℤ) :
    (cyclicDerivedFreeAdjunction F).unit.app (DerivedCategory.Q.obj K) ≫
        (forget F).mapDerivedCategory.map
          ((Free.functor F).mapDerivedCategoryFactors.hom.app K) ≫
        (forget F).mapDerivedCategoryFactors.hom.app
          (((Free.functor F).mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map (((Free.adjunction F).mapHomologicalComplex (.up ℤ)).unit.app K) := by
  simp only [cyclicDerivedFreeAdjunction, Adjunction.mapExactDerivedCategory,
    Adjunction.localization_unit_app]
  change (DerivedCategory.Q.map _ ≫
    (forget F).mapDerivedCategoryFactors.inv.app _ ≫
    (forget F).mapDerivedCategory.map
      ((Free.functor F).mapDerivedCategoryFactors.inv.app K)) ≫ _ ≫ _ = _
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

private def freeUnit : (forget F).mapDerivedCategory ⟶
    cyclicDerivedFreeFunctor F ⋙ (forget F).mapDerivedCategory :=
  Functor.whiskerLeft (forget F).mapDerivedCategory (cyclicDerivedFreeAdjunction F).unit

private def forwardUnit : (forget F).mapDerivedCategory ⋙ F.mapDerivedCategory ⟶
    cyclicDerivedFreeFunctor F ⋙ (forget F).mapDerivedCategory :=
  Functor.whiskerRight (freeUnit F) F.mapDerivedCategory ≫
    Functor.whiskerLeft (cyclicDerivedFreeFunctor F) (cyclicDerivedStructure F).hom

private def underlyingComparison (K : CochainComplex (IsoAlgebra F) ℤ) :
    (forget F).mapDerivedCategory.obj
        ((cyclicDerivedFreeFunctor F).obj (DerivedCategory.Q.obj K)) ≅
      DerivedCategory.Q.obj (((forget F).mapHomologicalComplex (.up ℤ)).obj
        (((forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ)).obj K)) :=
  (forget F).mapDerivedCategory.mapIso (cyclicDerivedFreeComparison F K) ≪≫
    (forget F).mapDerivedCategoryFactors.app _

private lemma freeUnit_fac (K : CochainComplex (IsoAlgebra F) ℤ) :
    (freeUnit F).app (DerivedCategory.Q.obj K) ≫ (underlyingComparison F K).hom =
      (forget F).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map (((Free.adjunction F).mapHomologicalComplex (.up ℤ)).unit.app
          (((forget F).mapHomologicalComplex (.up ℤ)).obj K)) := by
  dsimp only [freeUnit, Functor.whiskerLeft_app, underlyingComparison,
    cyclicDerivedFreeComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  simp only [Functor.map_comp, Category.assoc]
  erw [← (cyclicDerivedFreeAdjunction F).unit.naturality_assoc]
  exact congrArg (_ ≫ ·) (unit_fac F _)

private lemma forwardUnit_fac (K : CochainComplex (IsoAlgebra F) ℤ) :
    (forwardUnit F).app (DerivedCategory.Q.obj K) ≫ (underlyingComparison F K).hom =
      F.mapDerivedCategory.map ((forget F).mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app
          (((forget F).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((F.mapHomologicalComplex (.up ℤ)).map
              (((Free.adjunction F).mapHomologicalComplex (.up ℤ)).unit.app
                (((forget F).mapHomologicalComplex (.up ℤ)).obj K)) ≫
            (NatTrans.mapHomologicalComplex (strNatIso F).hom (.up ℤ)).app
              (((forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ)).obj K)) := by
  dsimp only [forwardUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, underlyingComparison, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom]
  rw [Category.assoc, ← (cyclicDerivedStructure F).hom.naturality_assoc,
    structure_fac]
  simp only [Functor.comp_map]
  erw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  have hu := freeUnit_fac F K
  dsimp only [underlyingComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at hu
  simp only [Category.assoc] at hu ⊢
  erw [hu]
  erw [Functor.map_comp, Category.assoc, Functor.mapDerivedCategoryFactors_hom_naturality_assoc,
    ← DerivedCategory.Q.map_comp]

private lemma complex_difference (R : CyclicDerivedFreeResolution F)
    (K : CochainComplex (IsoAlgebra F) ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map
        (((Free.adjunction F).mapHomologicalComplex (.up ℤ)).unit.app
          (((forget F).mapHomologicalComplex (.up ℤ)).obj K)) ≫
        (NatTrans.mapHomologicalComplex (strNatIso F).hom (.up ℤ)).app
          (((forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ)).obj K) ≫
        ((forget F).mapHomologicalComplex (.up ℤ)).map
          ((R.d.mapHomologicalComplex (.up ℤ)).app K) =
      @HSub.hSub
        ((F.mapHomologicalComplex (.up ℤ)).obj
            (((forget F).mapHomologicalComplex (.up ℤ)).obj K) ⟶
          ((forget F).mapHomologicalComplex (.up ℤ)).obj
            (((forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ)).obj K))
        ((F.mapHomologicalComplex (.up ℤ)).obj
            (((forget F).mapHomologicalComplex (.up ℤ)).obj K) ⟶
          ((forget F).mapHomologicalComplex (.up ℤ)).obj
            (((forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ)).obj K))
        ((F.mapHomologicalComplex (.up ℤ)).obj
            (((forget F).mapHomologicalComplex (.up ℤ)).obj K) ⟶
          ((forget F).mapHomologicalComplex (.up ℤ)).obj
            (((forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ)).obj K)) inferInstance
        ((F.mapHomologicalComplex (.up ℤ)).map
          (((Free.adjunction F).mapHomologicalComplex (.up ℤ)).unit.app
            (((forget F).mapHomologicalComplex (.up ℤ)).obj K)) ≫
          (NatTrans.mapHomologicalComplex (strNatIso F).hom (.up ℤ)).app
            (((forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ)).obj K))
        ((NatTrans.mapHomologicalComplex (strNatIso F).hom (.up ℤ)).app K ≫
          (((Free.adjunction F).mapHomologicalComplex (.up ℤ)).unit.app
            (((forget F).mapHomologicalComplex (.up ℤ)).obj K))) := by
  ext n
  simp only [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f,
    Adjunction.mapHomologicalComplex, heart_unit, strNatIso_hom_app]
  have h := heart_difference F R (K.X n)
  rw [heart_unit] at h
  dsimp only [Functor.mapHomologicalComplex, Functor.comp_obj, forget_obj,
    Free.functor, Free.algebra, str_hom, mk_obj] at h ⊢
  exact h

private lemma differential_fac (R : CyclicDerivedFreeResolution F)
    (K : CochainComplex (IsoAlgebra F) ℤ) :
    (forget F).mapDerivedCategory.map (R.differential.app (DerivedCategory.Q.obj K)) ≫
        (underlyingComparison F K).hom =
      (underlyingComparison F K).hom ≫ DerivedCategory.Q.map
        (((forget F).mapHomologicalComplex (.up ℤ)).map
          ((R.d.mapHomologicalComplex (.up ℤ)).app K)) := by
  dsimp only [underlyingComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  erw [← Functor.map_comp_assoc, R.differential_fac, Functor.map_comp,
    Category.assoc, Functor.mapDerivedCategoryFactors_hom_naturality]
  exact (Category.assoc _ _ _).symm

private lemma derived_difference (R : CyclicDerivedFreeResolution F)
    (M : DerivedCategory (IsoAlgebra F)) :
    (forwardUnit F).app M ≫ (forget F).mapDerivedCategory.map (R.differential.app M) =
      (forwardUnit F).app M - (cyclicDerivedStructure F).hom.app M ≫ (freeUnit F).app M := by
  have h : forwardUnit F ≫ Functor.whiskerRight R.differential (forget F).mapDerivedCategory =
      forwardUnit F - (cyclicDerivedStructure F).hom ≫ freeUnit F := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (IsoAlgebra F) (.up ℤ))
    intro K
    change (forwardUnit F).app (DerivedCategory.Q.obj K) ≫
        (forget F).mapDerivedCategory.map (R.differential.app (DerivedCategory.Q.obj K)) =
      (forwardUnit F).app (DerivedCategory.Q.obj K) -
        (cyclicDerivedStructure F).hom.app (DerivedCategory.Q.obj K) ≫
          (freeUnit F).app (DerivedCategory.Q.obj K)
    apply (cancel_mono (underlyingComparison F K).hom).1
    rw [Category.assoc, differential_fac, ← Category.assoc, forwardUnit_fac,
      Preadditive.sub_comp]
    simp only [Category.assoc]
    erw [forwardUnit_fac, freeUnit_fac]
    conv_rhs => arg 2; rw [← Category.assoc, structure_fac]
    simp only [Category.assoc]
    erw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    simp only [Category.assoc]
    erw [complex_difference]
    simp only [Functor.map_sub, Preadditive.comp_sub]
  exact NatTrans.congr_app h M

private lemma adjunct_action (M N P : DerivedCategory (IsoAlgebra F)) (r : ℤ)
    (c : (forget F).mapDerivedCategory.obj P ⟶ ((forget F).mapDerivedCategory.obj N)⟦r⟧)
    (hc : (cyclicDerivedStructure F).hom.app P ≫ c =
      F.mapDerivedCategory.map c ≫
        (F.mapDerivedCategory.commShiftIso r).hom.app ((forget F).mapDerivedCategory.obj N) ≫
        ((cyclicDerivedStructure F).hom.app N)⟦r⟧')
    (f : (cyclicDerivedFreeFunctor F).obj M ⟶ P) :
    cyclicDerivedHomAction F M N r
        ((freeUnit F).app M ≫ (forget F).mapDerivedCategory.map f ≫ c) =
      (cyclicDerivedStructure F).inv.app M ≫ (forwardUnit F).app M ≫
        (forget F).mapDerivedCategory.map f ≫ c := by
  change ((cyclicDerivedStructure F).inv.app M ≫
      F.mapDerivedCategory.map ((freeUnit F).app M ≫
        (forget F).mapDerivedCategory.map f ≫ c)) ≫
      ((F.mapDerivedCategory.commShiftIso r).hom.app ((forget F).mapDerivedCategory.obj N) ≫
        ((cyclicDerivedStructure F).hom.app N)⟦r⟧') = _
  simp only [Functor.map_comp, Category.assoc]
  rw [← hc]
  erw [(cyclicDerivedStructure F).hom.naturality_assoc]
  simp only [forwardUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc]

private lemma adjunct_difference (R : CyclicDerivedFreeResolution F)
    (M N P : DerivedCategory (IsoAlgebra F)) (r : ℤ)
    (c : (forget F).mapDerivedCategory.obj P ⟶ ((forget F).mapDerivedCategory.obj N)⟦r⟧)
    (hc : (cyclicDerivedStructure F).hom.app P ≫ c =
      F.mapDerivedCategory.map c ≫
        (F.mapDerivedCategory.commShiftIso r).hom.app ((forget F).mapDerivedCategory.obj N) ≫
        ((cyclicDerivedStructure F).hom.app N)⟦r⟧')
    (f : (cyclicDerivedFreeFunctor F).obj M ⟶ P) :
    cyclicDerivedHomAction F M N r
        ((freeUnit F).app M ≫
          (forget F).mapDerivedCategory.map (R.differential.app M ≫ f) ≫ c) =
      cyclicDerivedHomAction F M N r
          ((freeUnit F).app M ≫ (forget F).mapDerivedCategory.map f ≫ c) -
        ((freeUnit F).app M ≫ (forget F).mapDerivedCategory.map f ≫ c) := by
  rw [adjunct_action F M N P r c hc, adjunct_action F M N P r c hc,
    Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc ((forwardUnit F).app M)
    ((forget F).mapDerivedCategory.map (R.differential.app M)), derived_difference]
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
    Iso.inv_hom_id_app_assoc]

omit [IsGrothendieckAbelian.{v} C] in
private lemma structure_shift (N : DerivedCategory (IsoAlgebra F)) (r : ℤ) :
    (cyclicDerivedStructure F).hom.app (N⟦r⟧) ≫
        ((forget F).mapDerivedCategory.commShiftIso r).hom.app N =
      F.mapDerivedCategory.map (((forget F).mapDerivedCategory.commShiftIso r).hom.app N) ≫
        (F.mapDerivedCategory.commShiftIso r).hom.app ((forget F).mapDerivedCategory.obj N) ≫
        ((cyclicDerivedStructure F).hom.app N)⟦r⟧' := by
  let : NatTrans.CommShift (cyclicDerivedStructure F).hom ℤ := by
    dsimp only [cyclicDerivedStructure, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
    (NatTrans.shift_app_comm (cyclicDerivedStructure F).hom r N).symm

omit [IsGrothendieckAbelian.{v} C] in
private lemma structure_zero (N : DerivedCategory (IsoAlgebra F)) :
    (cyclicDerivedStructure F).hom.app N ≫
        (shiftFunctorZero (DerivedCategory C) ℤ).inv.app
          ((forget F).mapDerivedCategory.obj N) =
      F.mapDerivedCategory.map ((shiftFunctorZero (DerivedCategory C) ℤ).inv.app
          ((forget F).mapDerivedCategory.obj N)) ≫
        (F.mapDerivedCategory.commShiftIso (0 : ℤ)).hom.app
          ((forget F).mapDerivedCategory.obj N) ≫
        ((cyclicDerivedStructure F).hom.app N)⟦(0 : ℤ)⟧' := by
  simp only [Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  exact (shiftFunctorZero (DerivedCategory C) ℤ).inv.naturality
    ((cyclicDerivedStructure F).hom.app N)

private lemma coordinates_zero_apply (M N : DerivedCategory (IsoAlgebra F))
    (f : (cyclicDerivedFreeFunctor F).obj M ⟶ N) :
    cyclicDerivedFreeHomEquiv F M N f =
      (freeUnit F).app M ≫ (forget F).mapDerivedCategory.map f ≫
        (shiftFunctorZero (DerivedCategory C) ℤ).inv.app
          ((forget F).mapDerivedCategory.obj N) := by
  change 𝟙 _ ≫ (cyclicDerivedFreeAdjunction F).homEquiv _ _ f ≫ _ = _
  rw [Category.id_comp, Adjunction.homEquiv_unit, Category.assoc]
  rfl

private lemma coordinates_shift_apply (M N : DerivedCategory (IsoAlgebra F))
    (f : ((cyclicDerivedFreeFunctor F).obj M)⟦(1 : ℤ)⟧ ⟶ N) :
    cyclicDerivedFreeShiftedHomEquiv F M N f =
      (freeUnit F).app M ≫ (forget F).mapDerivedCategory.map
          ((cyclicDerivedFreeShiftAdjunction F).homEquiv _ N f) ≫
        ((forget F).mapDerivedCategory.commShiftIso (-1 : ℤ)).hom.app N := by
  rw [cyclicDerivedFreeShiftedHomEquiv_apply, Adjunction.homEquiv_unit, Category.assoc]
  rfl

/-- Evaluation of the cyclic difference on a free adjunct gives 1 minus the inverse
cyclic action. Equivalently, evaluating it on T(u) gives -(1-T)(u). This is a
calculation of the differential, with no assertion about exactness or a boundary.

Proof: first work on chain representatives. An adjunct of u has summand n equal
to theta_N,n composed with the n-th translate of u. Precomposing by d and evaluating
on summand zero gives u minus its summand -1, namely (1-T⁻¹)u, by the prescribed
summand formula for d. Applying this to T(u) gives T(u)-u. Localize the calculation
using differential_fac and the standard exact-functor factorization isomorphisms.
Naturality allows replacement of representatives by their localization isomorphisms.
For the second equation move the source shift to the target using shiftEquiv and
apply the same calculation with target N[-1]; the shift comparison is precisely
the one in cyclicDerivedHomAction. There is no rotation sign in precomposition
by d[1], so the result is again T(u)-u. No boundedness is used.
Source: parent calculus step 2, free-resolution summand calculation, Stacks 0149, 0152
(blueprint: lem-sf-cyclic-free-defect-coordinates). -/
theorem cyclicDerivedFreeDefect_coordinates (R : CyclicDerivedFreeResolution F)
    (M N : DerivedCategory (IsoAlgebra F)) :
    (∀ u : CyclicDerivedHom F M N 0,
      cyclicDerivedFreeHomEquiv F M N
        (R.differential.app M ≫ (cyclicDerivedFreeHomEquiv F M N).symm
          (cyclicDerivedHomAction F M N 0 u)) = -cyclicDerivedHomDefect F M N 0 u) ∧
    (∀ u : CyclicDerivedHom F M N (-1),
      cyclicDerivedFreeShiftedHomEquiv F M N
        ((R.differential.app M)⟦(1 : ℤ)⟧' ≫
          (cyclicDerivedFreeShiftedHomEquiv F M N).symm
            (cyclicDerivedHomAction F M N (-1) u)) =
        -cyclicDerivedHomDefect F M N (-1) u) := by
  have h0 (f : (cyclicDerivedFreeFunctor F).obj M ⟶ N) :
      cyclicDerivedHomAction F M N 0
          (cyclicDerivedFreeHomEquiv F M N (R.differential.app M ≫ f)) =
        cyclicDerivedHomAction F M N 0 (cyclicDerivedFreeHomEquiv F M N f) -
          cyclicDerivedFreeHomEquiv F M N f := by
    simp only [coordinates_zero_apply]
    exact adjunct_difference F R M N N 0 _ (structure_zero F N) f
  have h1 (f : ((cyclicDerivedFreeFunctor F).obj M)⟦(1 : ℤ)⟧ ⟶ N) :
      cyclicDerivedHomAction F M N (-1)
          (cyclicDerivedFreeShiftedHomEquiv F M N
            ((R.differential.app M)⟦(1 : ℤ)⟧' ≫ f)) =
        cyclicDerivedHomAction F M N (-1) (cyclicDerivedFreeShiftedHomEquiv F M N f) -
          cyclicDerivedFreeShiftedHomEquiv F M N f := by
    simp only [coordinates_shift_apply]
    rw [Adjunction.homEquiv_naturality_left]
    exact adjunct_difference F R M N (N⟦(-1 : ℤ)⟧) (-1) _
      (structure_shift F N (-1)) _
  constructor
  · intro u
    apply (cyclicDerivedHomAction_bijective F M N 0).injective
    rw [h0, AddEquiv.apply_symm_apply]
    simp [cyclicDerivedHomDefect, map_sub, neg_sub]
  · intro u
    apply (cyclicDerivedHomAction_bijective F M N (-1)).injective
    rw [h1, AddEquiv.apply_symm_apply]
    simp [cyclicDerivedHomDefect, map_sub, neg_sub]

end CategoryTheory.Endofunctor.IsoAlgebra
