/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.PointModelFreeModule
public import WeilConjectures.AlgebraicGeometry.PointModelPullbackFunctor
public import WeilConjectures.AlgebraicGeometry.PointModelRestrictionModule
import WeilConjectures.AlgebraicGeometry.CoefficientSliceRestrictionIso
import all WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealization
import all WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Transport of a discrete point presentation to the coefficient slice

Source: Stacks, Tags 03CY and 00YV.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local instance 2000] AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafMonoidalClosed
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

private noncomputable def smallRegularIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (smallModules X R).obj (Mod.regular R) ≅
      SheafOfModules.unit (siteModuleRings (smallRing X R)) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun V ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
  · intro r
    ext x
    rfl
  · intro V W f
    rfl

private noncomputable def resRegularIso
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    {R S : Sheaf J CommRingCat.{u + 1}} (c : R ≅ S) :
    (ConstantCompletion.res c.hom).obj (SheafOfModules.unit (siteModuleRings S)) ≅
      SheafOfModules.unit (siteModuleRings R) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · let eV := ((sheafToPresheaf J RingCat.{u + 1}).mapIso
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)).app V
    exact ModuleCat.restrictScalarsIsoOfEquiv eV.ringCatIsoToRingEquiv
  · intro V W f
    ext s
    change c.inv.hom.app W (S.obj.map f s) = R.obj.map f (c.inv.hom.app V s)
    exact ConcreteCategory.congr_hom (c.inv.hom.naturality f) s

attribute [local instance] SheafOfModules.monoidalCategory
private noncomputable def fixedRegularIso
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (k : Type (u + 1)) [CommRing k] :
    (coefficientModelFixedScalars J k).obj
        (SheafOfModules.unit (siteModuleRings (ConstantCompletion.constant J k))) ≅
      (constantSheaf J (ModuleCat.{u + 1} k)).obj (ModuleCat.of k k) := by
  letI : (ConstantScalarRestriction.restriction J k).Monoidal :=
    (ConstantScalarRestriction.ordinary J k).braided.toMonoidal
  let i : ConstantScalarRestriction.restriction J k ≅ coefficientModelFixedScalars J k := by
    simpa only [ConstantScalarRestriction.restriction, ringRestriction,
      coefficientRingIso, Iso.app_inv]
      using restrictionIso J k
  letI : (coefficientModelFixedScalars J k).Monoidal := Functor.Monoidal.transport i
  exact (Functor.Monoidal.εIso (coefficientModelFixedScalars J k)).symm ≪≫
    ConstantScalarRestriction.fixedUnitIso J k
private theorem modelBaseChange_preservesFiniteLimits {X Y : Scheme.{u}} (f : Y ⟶ X) :
    PreservesFiniteLimits (Scheme.coefficientProEtaleModelBaseChange.{u, u} f) := by
  dsimp [Scheme.coefficientProEtaleModelBaseChange]
  have : PreservesFiniteLimits
      (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt) :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse)
  have : PreservesFiniteLimits (Scheme.proEtaleBaseChange f) := inferInstance
  have : PreservesFiniteLimits
      (AsSmall.up : Y.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, u} Y) :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).functor)
  infer_instance

private noncomputable def fixedConstantPullbackIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (k : Type (u + 1)) [CommRing k] (M : ModuleCat.{u + 1} k) :
    (Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k).obj
        ((constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X) _).obj M) ≅
      (constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} Y) _).obj M := by
  let F := Scheme.coefficientProEtaleModelBaseChange.{u, u} f
  have : PreservesFiniteLimits F := modelBaseChange_preservesFiniteLimits f
  have : (AsSmall.up : X.ProEt ⥤
      Scheme.coefficientProEtaleSiteModel.{u, u} X).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsEquivalence
  let T : Scheme.coefficientProEtaleSiteModel.{u, u} X := AsSmall.up.obj
    (MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance))
  let hT : IsTerminal T := (MorphismProperty.Over.mkIdTerminal @WeaklyEtale X).isTerminalObj
    (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, u} X)
  exact ((Functor.sheafPullbackConstruction.sheafPullbackIso F (ModuleCat.{u + 1} k)
      (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (Scheme.coefficientProEtaleModelTopology.{u, u} Y)).symm.app _) ≪≫
    (F.constantSheafsheafPullbackIso (ModuleCat.{u + 1} k) _ _ hT
      (hT.isTerminalObj F)).app M

private theorem resEquivalence
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    {R S : Sheaf J CommRingCat.{u + 1}} (c : R ≅ S) :
    (ConstantCompletion.res c.hom).IsEquivalence := by
  let a := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c
  let e := CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars.{u + 1} a.hom)
    (SheafOfModules.restrictScalars.{u + 1} a.inv)
    (ConstantScalarRestriction.restrictCancelIso J a.inv a.hom a.inv_hom_id).symm
    (ConstantScalarRestriction.restrictCancelIso J a.hom a.inv a.hom_inv_id)
  exact e.isEquivalence_functor

private noncomputable def modelRegularIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X R) :
    (coefficientModelFixedScalars _ k).obj
        ((smallModules X R ⋙ ConstantCompletion.res c.hom).obj (Mod.regular R)) ≅
      (constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (ModuleCat.{u + 1} k)).obj (ModuleCat.of k k) :=
  (coefficientModelFixedScalars _ k).mapIso
    ((ConstantCompletion.res c.hom).mapIso (smallRegularIso X R) ≪≫ resRegularIso _ c) ≪≫
      fixedRegularIso _ k

private noncomputable def mapFreeIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (k : Type (u + 1)) [CommRing k]
    (F : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ ⥤
      Sheaf J (ModuleCat.{u + 1} k)) [F.Additive]
    (i : F.obj (Mod.regular Λ) ≅ (constantSheaf J (ModuleCat.{u + 1} k)).obj
      (ModuleCat.of k k)) (n : ℕ) :
    F.obj (pointModelFree Λ n) ≅
      (constantSheaf J (ModuleCat.{u + 1} k)).obj (ModuleCat.of k (Fin n → k)) := by
  exact F.mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
    biproduct.mapIso (fun _ ↦ i) ≪≫
    ((constantSheaf J (ModuleCat.{u + 1} k)).mapBiproduct
      (fun _ : Fin n ↦ ModuleCat.of k k)).symm ≪≫
    (constantSheaf J (ModuleCat.{u + 1} k)).mapIso (ModuleCat.biproductIsoPi _)

private noncomputable def modelOnSlice {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X R) (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y) :=
  smallModules X R ⋙ ConstantCompletion.res c.hom ⋙ coefficientModelFixedScalars _ k ⋙
    Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k ⋙
      (Scheme.coefficientProEtaleModelTopology.{u, u} Y).overPullback (ModuleCat.{u + 1} k) U

private theorem smallEquivalence (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (smallModules X R).IsEquivalence := by
  let A := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) R)
  let B := ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
    X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)).obj A
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsContinuous
      (Scheme.ProEt.topology X) (Scheme.coefficientProEtaleModelTopology.{u, u} X) :=
    Scheme.coefficientProEtaleModelUp_isContinuous.{u, u} X
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsContinuous
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X) := by
    change (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).IsContinuous
      ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
        X.ProEt).inducedTopology (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X)
    infer_instance
  let e := SheafOfModules.pushforwardPushforwardEquivalence
    (J := Scheme.ProEt.topology X)
    (K := Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)) (𝟙 A) (𝟙 B)
    (by ext U; dsimp [AsSmall.equiv]; erw [B.obj.map_id]; rfl)
    (by ext U; dsimp [AsSmall.equiv]; erw [A.obj.map_id]; rfl)
  have : e.inverse.IsEquivalence := e.isEquivalence_inverse
  exact inferInstanceAs
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R).functor ⋙ e.inverse).IsEquivalence

private theorem modelOnSlice_preserves {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X R) (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y) :
    PreservesFiniteColimits (modelOnSlice f R k c U) := by
  have := smallEquivalence X R
  have := resEquivalence _ c
  have := coefficientModelFixedScalars_isEquivalence
    (Scheme.coefficientProEtaleModelTopology.{u, u} X) k
  let P := Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k
  have : PreservesColimitsOfSize.{u + 1, u + 1} P :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Scheme.coefficientProEtaleModelBaseChange.{u, u} f) (ModuleCat.{u + 1} k)
      (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (Scheme.coefficientProEtaleModelTopology.{u, u} Y)).leftAdjoint_preservesColimits
  let Q := (Scheme.coefficientProEtaleModelTopology.{u, u} Y).overPullback
    (ModuleCat.{u + 1} k) U
  have : PreservesColimitsOfSize.{u + 1, u + 1} Q :=
    ((Over.forget U).sheafAdjunctionCocontinuous (ModuleCat.{u + 1} k)
      ((Scheme.coefficientProEtaleModelTopology.{u, u} Y).over U)
      (Scheme.coefficientProEtaleModelTopology.{u, u} Y)).leftAdjoint_preservesColimits
  exact inferInstanceAs (PreservesFiniteColimits
    (smallModules X R ⋙ ConstantCompletion.res c.hom ⋙ coefficientModelFixedScalars _ k ⋙
      P ⋙ Q))

private theorem pointPullback_preservesFiniteColimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Z : Scheme.{u}) :
    PreservesFiniteColimits (pointModelPullbackFunctor Λ Z) := by
  have : (upperStarFromPoint Z).IsLeftAdjoint := by
    unfold upperStarFromPoint
    exact (pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Z))).isLeftAdjoint
  unfold pointModelPullbackFunctor
  infer_instance

private noncomputable def pointRegularIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    (pointModelPullbackFunctor Λ X).obj (Mod.regular Λ) ≅
      Mod.regular (condensedRingObj Λ X) := by
  exact Mod.isoMk (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp])

private theorem additive_of_finiteColimits
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D] [HasBinaryBiproducts C]
    (F : C ⥤ D) [PreservesFiniteColimits F] : F.Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  exact Functor.additive_of_preservesBinaryBiproducts F

private noncomputable def sliceConstantIso
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (k : Type (u + 1)) [CommRing k] (U : C) (M : ModuleCat.{u + 1} k) :
    (J.overPullback (ModuleCat.{u + 1} k) U).obj
      ((constantSheaf J (ModuleCat.{u + 1} k)).obj M) ≅
    (constantSheaf (J.over U) (ModuleCat.{u + 1} k)).obj M := by
  exact (J.overPullbackConstantSheafIso (ModuleCat.{u + 1} k) U).app M

private noncomputable def modelOnSliceRegularIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X R) (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y) :
    (modelOnSlice f R k c U).obj (Mod.regular R) ≅
      (constantSheaf ((Scheme.coefficientProEtaleModelTopology.{u, u} Y).over U)
        (ModuleCat.{u + 1} k)).obj (ModuleCat.of k k) := by
  exact ((Scheme.coefficientProEtaleModelTopology.{u, u} Y).overPullback
      (ModuleCat.{u + 1} k) U).mapIso
      ((Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k).mapIso
        (modelRegularIso X R k c) ≪≫ fixedConstantPullbackIso f k (ModuleCat.of k k)) ≪≫
      sliceConstantIso _ k U (ModuleCat.of k k)

private noncomputable def pointOnSliceRegularIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X))
    (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y) :
    (pointModelPullbackFunctor Λ X ⋙ modelOnSlice f (condensedRingObj Λ X) k c U).obj
      (Mod.regular Λ) ≅
      (constantSheaf ((Scheme.coefficientProEtaleModelTopology.{u, u} Y).over U)
        (ModuleCat.{u + 1} k)).obj (ModuleCat.of k k) :=
  (modelOnSlice f (condensedRingObj Λ X) k c U).mapIso (pointRegularIso Λ X) ≪≫
    modelOnSliceRegularIso f (condensedRingObj Λ X) k c U

private theorem presentationOfMappedFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (k : Type (u + 1)) [CommRing k]
    (F : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ ⥤
      Sheaf J (ModuleCat.{u + 1} k)) [F.Additive] [PreservesFiniteColimits F]
    (i : F.obj (Mod.regular Λ) ≅ (constantSheaf J (ModuleCat.{u + 1} k)).obj
      (ModuleCat.of k k)) (m n : ℕ)
    (d : pointModelFree Λ m ⟶ pointModelFree Λ n) :
    ∃ a : (constantSheaf J (ModuleCat.{u + 1} k)).obj (ModuleCat.of k (Fin m → k)) ⟶
      (constantSheaf J (ModuleCat.{u + 1} k)).obj (ModuleCat.of k (Fin n → k)),
      Nonempty (F.obj (cokernel d) ≅ cokernel a) := by
  let im := mapFreeIso Λ J k F i m
  let jn := mapFreeIso Λ J k F i n
  let a := im.inv ≫ F.map d ≫ jn.hom
  refine ⟨a, ⟨PreservesCokernel.iso F d ≪≫ cokernel.mapIso _ a im jn ?_⟩⟩
  simp only [a, Iso.hom_inv_id_assoc]

private theorem restrictionOfPointIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (Q : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    Nonempty (pointModelRestriction Λ f ((pointModelPullbackFunctor Λ X).obj Q) g ≅
      (pointModelPullbackFunctor Λ Z).obj Q) := by
  let : HasCoequalizers (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) := inferInstance
  let (T : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft T) :=
    AlgebraicGeometry.ProEtale.preservesColimitsOfSize_tensorLeft_sheaf Ab.{u + 1} Z T
  let (T : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight T) :=
    AlgebraicGeometry.ProEtale.preservesColimitsOfSize_tensorRight_sheaf Ab.{u + 1} Z T
  exact ⟨(Functor.mapModCompExtendScalarsIso (upperStarFromPoint X)
    (upperStar Ab.{u + 1} (g ≫ f)) (upperStarFromPointComp (g ≫ f)).hom Λ).app Q⟩

attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver
attribute [local instance 20000] CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit
  CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape
attribute [local instance 2000] CategoryTheory.Sheaf.instHasColimitsOfSize
  CategoryTheory.Sheaf.instHasColimitsOfShape CategoryTheory.Sheaf.instHasFiniteColimits
  CategoryTheory.Sheaf.hasLimitsOfSize CategoryTheory.Sheaf.instHasFiniteLimits
attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar
  upperStar lowerStar CondensedRing.lowerStar CategoryTheory.Sheaf.monoidalCategory
  CondensedRing.upperStarComp upperStarFromPointComp Mod.extendScalarsIsoComapInv
  laxBraided_upperStarFromPoint monoidal_upperStarFromPoint
  smallModules coefficientModelFixedScalars Scheme.coefficientProEtaleFixedModulePullback
  pointModelFree pointModelPullbackFunctor

/-- The displayed point presentation transports to a finite matrix presentation on the slice.
This is the section reconstruction, constant-sheaf pullback, and scalar-restriction step of
Stacks Tags 03CY and 00YV; it is strictly the first step of the refinement argument and does
not include the local lifting of matrix coefficients.

Source: Stacks, Modules on Sites, Tag 03CY; Sites, Tag 00YV.
(auxiliary; not a blueprint node).

Proof: compose point pullback on X with section reconstruction, the small-site equivalence,
restriction of scalars along c, fixed-scalar reconstruction, scheme inverse image and slice
restriction. This functor preserves finite colimits. The regular-module comparison and c,
followed by constant-sheaf pullback, identify its regular module with the constant k-module.
Finite biproducts identify its two free terms, so conjugating the image of d gives the
required matrix a. Preservation of cokernels identifies the image of coker d with coker a.
Point-pullback composition and the given hN identify the internal restrictions of N and
the point cokernel on X. Apply coefficient-slice invariance to this isomorphism, and
compose with the proved cokernel comparison. The separate equivalence e is not needed
once the ring-sheaf isomorphism c is given.
-/
theorem discrete_point_presentation_transport
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : Type u) [CommRing A] (k : Type (u + 1)) [CommRing k]
    (e : ULift.{u + 1} A ≃+* k)
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj (discreteObj A) X))
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj A) X))
    (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y)
    (m n : ℕ)
    (d : pointModelFree (discreteObj A) m ⟶ pointModelFree (discreteObj A) n)
    (hN : Nonempty
        (pointModelRestriction (discreteObj A) f N (AsSmall.down.obj U).hom ≅
          (pointModelPullbackFunctor (discreteObj A) (AsSmall.down.obj U).left).obj (cokernel d))) :
    ∃ a : (constantSheaf
        ((Scheme.coefficientProEtaleModelTopology.{u, u} Y).over U)
        (ModuleCat.{u + 1} k)).obj (ModuleCat.of k (Fin m → k)) ⟶
      (constantSheaf
        ((Scheme.coefficientProEtaleModelTopology.{u, u} Y).over U)
        (ModuleCat.{u + 1} k)).obj (ModuleCat.of k (Fin n → k)),
      Nonempty (((Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k).obj
          ((coefficientModelFixedScalars _ k).obj
            ((smallModules X (condensedRingObj (discreteObj A) X) ⋙
              ConstantCompletion.res c.hom).obj N))).over U ≅ cokernel a) := by
  classical
  -- c supplies the scalar identification; retain e in the unchanged public interface.
  let _coefficientEquivalence := e
  let Λ := discreteObj A
  let R := condensedRingObj Λ X
  let P := pointModelPullbackFunctor Λ X
  let G := modelOnSlice f R k c U
  let F := P ⋙ G
  have : PreservesFiniteColimits P := pointPullback_preservesFiniteColimits Λ X
  have : PreservesFiniteColimits G := modelOnSlice_preserves f R k c U
  have : PreservesFiniteColimits F := inferInstance
  have : F.Additive := additive_of_finiteColimits F
  have : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  obtain ⟨a, ⟨ia⟩⟩ := presentationOfMappedFree Λ _ k F
    (pointOnSliceRegularIso Λ f k c U) m n d
  refine ⟨a, ?_⟩
  obtain ⟨h⟩ := hN
  obtain ⟨iQ⟩ := restrictionOfPointIso Λ (Z := (AsSmall.down.obj U).left)
    f (AsSmall.down.obj U).hom (cokernel d)
  have hNM : Nonempty (pointModelRestriction Λ f N (AsSmall.down.obj U).hom ≅
      pointModelRestriction Λ f (P.obj (cokernel d)) (AsSmall.down.obj U).hom) :=
    ⟨h ≪≫ iQ.symm⟩
  obtain ⟨iN⟩ := coefficient_slice_iso_of_internal_restriction_iso
    Λ f k c N (P.obj (cokernel d)) U hNM
  exact ⟨iN ≪≫ ia⟩

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
