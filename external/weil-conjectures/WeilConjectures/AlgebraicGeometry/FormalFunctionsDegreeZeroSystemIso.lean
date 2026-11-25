/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Ext

public import WeilConjectures.AlgebraicGeometry.FormalFibreCohomology
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapZeroAugmentation
import WeilConjectures.AlgebraicGeometry.SchemeModulesEnoughInjectives
/-! # Degree-zero comparison of the formal fibre systems

Source: Stacks Project, Cohomology of Schemes, Lemma 02OD
(blueprint: lem-weil-pbc-formal-functions-degree-zero-system-iso).
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section

namespace AlgebraicGeometry

attribute [local instance] Scheme.Modules.enoughInjectives

private def zeroIso (Z : Scheme.{u}) (F : Z.Modules) :
    (RingedSpace.moduleCohomology Z.toRingedSpace 0).obj F ≅
      (RingedSpace.globalSectionsFunctor Z.toRingedSpace).obj F := by
  let S := RingedSpace.globalSectionsFunctor Z.toRingedSpace
  have : PreservesFiniteLimits S :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings Z.toRingedSpace) (op ⊤)))
  exact S.rightDerivedZeroIsoSelf.app F

private theorem degreeZero_naturality {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : Y.Modules} {F : X.Modules} (φ : G ⟶ (Scheme.Modules.pushforward h).obj F) :
    Scheme.Modules.moduleCohomologyFMap h φ 0 ≫
        (forget₂ _ AddCommGrpCat).map (zeroIso X F).hom =
      (forget₂ _ AddCommGrpCat).map (zeroIso Y G).hom ≫
        (forget₂ _ AddCommGrpCat).map
          ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).map φ) ≫
        F.presheaf.map (eqToHom (by simp) : (⊤ : X.Opens) ⟶ h ⁻¹ᵁ (⊤ : Y.Opens)).op := by
  let a := (forget₂ _ AddCommGrpCat).mapIso (zeroIso Y G)
  let b := (forget₂ _ AddCommGrpCat).mapIso (zeroIso X F)
  let s := (forget₂ _ AddCommGrpCat).map
      ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).map φ) ≫
    F.presheaf.map (eqToHom (by simp) : (⊤ : X.Opens) ⟶ h ⁻¹ᵁ (⊤ : Y.Opens)).op
  have ha : a.inv ≫ Scheme.Modules.moduleCohomologyFMap h φ 0 = s ≫ b.inv :=
    by
      have ht := Scheme.Modules.ModuleCohomologyFMapData.map_zero_augmentation
        (Classical.choice (Scheme.Modules.moduleCohomologyFMapData_nonempty h G F φ))
      refine ht.trans ?_
      change _ = (forget₂ _ AddCommGrpCat).map
          ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).map φ) ≫
        F.presheaf.map (eqToHom (by simp) : (⊤ : X.Opens) ⟶ h ⁻¹ᵁ (⊤ : Y.Opens)).op ≫
        (forget₂ _ AddCommGrpCat).map
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app F)
      congr 1
      have hr : F.presheaf.map
          (eqToHom (by simp) : (⊤ : X.Opens) ⟶ h ⁻¹ᵁ (⊤ : Y.Opens)).op = 𝟙 _ := by
        change F.val.presheaf.map (𝟙 _) = 𝟙 _
        exact F.val.presheaf.map_id _
      rw [hr]
      exact (Category.id_comp _).symm
  change Scheme.Modules.moduleCohomologyFMap h φ 0 ≫ b.hom = a.hom ≫ s
  apply (cancel_epi a.inv).mp
  rw [Iso.inv_hom_id_assoc, ← Category.assoc, ha, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

private def levelIso {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    formalFibreCohomology f y (SheafOfModules.unit X.ringCatSheaf) 0 n ≅
      formalFibreSections f y n := by
  let Z := formalFibre f y n
  let S := RingedSpace.globalSectionsFunctor Z.toRingedSpace
  have hu := (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso (formalFibreι f y n)).1
  let e := zeroIso Z
    ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj
      (SheafOfModules.unit X.ringCatSheaf)) ≪≫
        S.mapIso (asIso (Scheme.Modules.tensorPullbackObjUnitToUnit (formalFibreι f y n)))
  exact (ModuleCat.restrictScalars ((formalFibreScalarMap f y n).comp
    (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (n + 1)).toRingHom)).mapIso e

private theorem levelIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    (forget₂ _ AddCommGrpCat).map (levelIso f y n).hom =
      (forget₂ _ AddCommGrpCat).map
          (zeroIso (formalFibre f y n)
            ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj
              (SheafOfModules.unit X.ringCatSheaf))).hom ≫
        (forget₂ _ AddCommGrpCat).map
          ((RingedSpace.globalSectionsFunctor (formalFibre f y n).toRingedSpace).map
            (Scheme.Modules.tensorPullbackObjUnitToUnit (formalFibreι f y n))) := rfl

private theorem unitPushforwardComp {Z W X : Scheme.{u}}
    (k : Z ⟶ X) (j : Z ⟶ W) (i : W ⟶ X) (h : k = j ≫ i) :
    SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom ≫
        (Scheme.Modules.pushforwardCongr h ≪≫
          (Scheme.Modules.pushforwardComp j i).symm).hom.app
            (SheafOfModules.unit Z.ringCatSheaf) =
      SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward i).map
          (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) := by
  subst k
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change Z.presheaf.map (𝟙 _)
      ((j ≫ i).app V.unop a) = j.app (i ⁻¹ᵁ V.unop) (i.app V.unop a)
  rw [Z.presheaf.map_id]
  change (j ≫ i).app V.unop a = _
  rw [Scheme.Hom.comp_app]
  rfl

private theorem unitTransition {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    formalFibreTransitionFMap f y (SheafOfModules.unit X.ringCatSheaf) n ≫
        (Scheme.Modules.pushforward (formalFibreTransition f y n)).map
          (Scheme.Modules.tensorPullbackObjUnitToUnit (formalFibreι f y n)) =
      Scheme.Modules.tensorPullbackObjUnitToUnit (formalFibreι f y (n + 1)) ≫
        SheafOfModules.unitToPushforwardObjUnit
          (formalFibreTransition f y n).toRingCatSheafHom := by
  let adj := Classical.choose
    (Scheme.Modules.exists_tensorPullbackAdjunction (formalFibreι f y (n + 1)))
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  change (adj.homEquiv _ _) ((adj.homEquiv _ _).symm _) ≫ _ = _
  rw [Equiv.apply_symm_apply]
  let c := Scheme.Modules.pushforwardCongr (formalFibreTransition_ι f y n) ≪≫
    (Scheme.Modules.pushforwardComp (formalFibreTransition f y n)
      (formalFibreι f y (n + 1))).symm
  change (_ ≫ c.hom.app _) ≫ _ = _
  rw [Category.assoc]
  erw [← c.hom.naturality]
  rw [← Category.assoc, (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso
    (formalFibreι f y n)).2]
  dsimp [adj, Scheme.Modules.tensorPullbackObjUnitToUnit]
  rw [Equiv.apply_symm_apply]
  exact unitPushforwardComp _ _ _ _

private theorem unitSectionsSquare {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : Y.Modules} {F : X.Modules} (φ : G ⟶ (Scheme.Modules.pushforward h).obj F)
    (eG : G ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (eF : F ⟶ SheafOfModules.unit X.ringCatSheaf)
    (he : φ ≫ (Scheme.Modules.pushforward h).map eF =
      eG ≫ SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) :
    (forget₂ _ AddCommGrpCat).map
        ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).map φ) ≫
      F.presheaf.map (eqToHom (by simp) : (⊤ : X.Opens) ⟶ h ⁻¹ᵁ (⊤ : Y.Opens)).op ≫
      (forget₂ _ AddCommGrpCat).map
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).map eF) =
    (forget₂ _ AddCommGrpCat).map
        ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).map eG) ≫
      AddCommGrpCat.ofHom h.appTop.hom.toAddMonoidHom := by
  ext s
  have hs := congrArg (fun k ↦ (k.val.app (op ⊤)).hom s) he
  have hn := PresheafOfModules.naturality_apply eF.val
    (eqToHom (by simp) : (⊤ : X.Opens) ⟶ h ⁻¹ᵁ (⊤ : Y.Opens)).op
    ((φ.val.app (op ⊤)).hom s)
  change (eF.val.app (op ⊤)).hom
      (F.val.map (eqToHom (by simp) : (⊤ : X.Opens) ⟶ h ⁻¹ᵁ (⊤ : Y.Opens)).op
        ((φ.val.app (op ⊤)).hom s)) = _
  rw [hn]
  change X.presheaf.map (eqToHom (by simp)).op
      ((eF.val.app (op (h ⁻¹ᵁ ⊤))).hom ((φ.val.app (op ⊤)).hom s)) = _
  change (eF.val.app (op (h ⁻¹ᵁ ⊤))).hom ((φ.val.app (op ⊤)).hom s) =
    h.app ⊤ ((eG.val.app (op ⊤)).hom s) at hs
  rw [hs]
  change X.presheaf.map (𝟙 _) _ = _
  rw [X.presheaf.map_id]
  rfl

private theorem degreeZero_unit_square {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : Y.Modules} {F : X.Modules} (φ : G ⟶ (Scheme.Modules.pushforward h).obj F)
    (eG : G ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (eF : F ⟶ SheafOfModules.unit X.ringCatSheaf)
    (he : φ ≫ (Scheme.Modules.pushforward h).map eF =
      eG ≫ SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) :
    Scheme.Modules.moduleCohomologyFMap h φ 0 ≫
      ((forget₂ _ AddCommGrpCat).map (zeroIso X F).hom ≫
        (forget₂ _ AddCommGrpCat).map
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).map eF)) =
    ((forget₂ _ AddCommGrpCat).map (zeroIso Y G).hom ≫
        (forget₂ _ AddCommGrpCat).map
          ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).map eG)) ≫
      AddCommGrpCat.ofHom h.appTop.hom.toAddMonoidHom := by
  rw [← Category.assoc, degreeZero_naturality h φ]
  simp only [Category.assoc]
  rw [unitSectionsSquare h φ eG eF he]

private theorem levelIso_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    formalFibreCohomologyTransition f y (SheafOfModules.unit X.ringCatSheaf) 0 n ≫
        (levelIso f y n).hom =
      (levelIso f y (n + 1)).hom ≫ formalFibreSectionsTransition f y n := by
  have h := degreeZero_unit_square (formalFibreTransition f y n)
    (formalFibreTransitionFMap f y (SheafOfModules.unit X.ringCatSheaf) n)
    (Scheme.Modules.tensorPullbackObjUnitToUnit (formalFibreι f y (n + 1)))
    (Scheme.Modules.tensorPullbackObjUnitToUnit (formalFibreι f y n)) (unitTransition f y n)
  apply (forget₂ _ AddCommGrpCat).map_injective
  rw [Functor.map_comp, Functor.map_comp, levelIso_hom, levelIso_hom]
  exact h

-- The unchanged existential statement deliberately has the predicate True.
set_option linter.unusedVariables false in
/-- Degree-zero fibre cohomology is naturally the section system for the unit
module.
Source: Stacks Project, Cohomology of Schemes, Lemma 02OD (degree zero).
Proof: Identify degree-zero module cohomology with sections using the canonical
augmentation. Apply sections to the canonical isomorphism from tensor pullback of
the unit module to the unit module, and restrict scalars to the completed local ring.
The adjunction characterization of the structure-sheaf map makes the transition
h-maps commute with these unit isomorphisms. The canonical augmentation square for
cohomology h-maps then proves compatibility with section pullback. Construct the
natural transformation with NatTrans.ofOpSequence; its components are isomorphisms,
so it is a natural isomorphism.
(blueprint: lem-weil-pbc-formal-functions-degree-zero-system-iso) -/
theorem formalFunctions_degreeZero_systemIso {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    ∃ b : formalFibreCohomologySystem f y (SheafOfModules.unit X.ringCatSheaf) 0 ≅
          formalFibreSectionsSystem f y, True := by
  let b : formalFibreCohomologySystem f y (SheafOfModules.unit X.ringCatSheaf) 0 ⟶
      formalFibreSectionsSystem f y :=
    NatTrans.ofOpSequence (fun n ↦ (levelIso f y n).hom) (by
      intro n
      simpa only [formalFibreCohomologySystem, formalFibreSectionsSystem,
        Functor.ofOpSequence_map_homOfLE_succ] using levelIso_naturality f y n)
  have : ∀ n, IsIso (b.app n) := by
    intro n
    change IsIso (levelIso f y n.unop).hom
    infer_instance
  have _hb : IsIso b := NatIso.isIso_of_isIso_app b
  exact ⟨asIso b, trivial⟩
end AlgebraicGeometry
