/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionTensorComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.Derived.DerivedTensorShiftDescent
import WeilConjectures.CategoryTheory.ProperBaseChange.SliceTensorIntegerShiftCompatibility
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Canonical projection-formula models

## References

* Stacks Project, Cohomology on Sites, Tags 07A4 and 07A6
* Stacks Project, Tags 03D7, 06YS, 06YU, 07A4 and 07A6
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

set_option backward.isDefEq.respectTransparency false in
private theorem canonical_unit_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ := by
  let inj := ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
  let E := HomotopyCategory.KInjectives.equivalence C
  let G := inj ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have hI : NatTrans.CommShift F.rightDerivedFunctorIsoKInjectives.inv ℤ :=
    Functor.CommShift.ofIso_compatibility F.rightDerivedFunctorIsoKInjectives.symm ℤ
  have hinv (Y : DerivedCategory C) :
      F.rightDerivedFunctorIsoKInjectives.inv.app Y =
        F.rightDerivedFunctorUnit.app (inj.obj (E.inverse.obj Y)) ≫
          F.rightDerivedFunctor.map (E.counit.app Y) := by
    simp [Functor.rightDerivedFunctorIsoKInjectives, inj, E]
  have heq : Functor.whiskerLeft inj F.rightDerivedFunctorUnit =
      (Functor.leftUnitor G).inv ≫ Functor.whiskerRight E.unitIso.hom G ≫
        (Functor.associator E.functor E.inverse G).hom ≫
        Functor.whiskerLeft E.functor F.rightDerivedFunctorIsoKInjectives.inv ≫
        (Functor.associator inj DerivedCategory.Qh F.rightDerivedFunctor).hom := by
    ext X
    have hn := F.rightDerivedFunctorUnit.naturality (inj.map (E.unit.app X))
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.leftUnitor_inv_app, hinv]
    dsimp only [G, E, inj] at hn ⊢
    simp only [Category.id_comp, Category.assoc]
    rw [← Category.assoc]
    erw [hn]
    erw [Category.comp_id]
    simp only [Functor.comp_map, Category.assoc]
    change _ = _ ≫ F.rightDerivedFunctor.map (E.functor.map (E.unit.app X)) ≫
      F.rightDerivedFunctor.map (E.counit.app (E.functor.obj X))
    rw [← Functor.map_comp]
    erw [E.functor_unit_comp, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  have : NatTrans.CommShift (Functor.whiskerLeft inj F.rightDerivedFunctorUnit) ℤ := by
    rw [heq]
    dsimp only [G, E, inj]
    infer_instance
  refine NatTrans.CommShift.of_whiskerLeft _ inj (fun K ↦ ?_)
  let J := E.inverse.obj (DerivedCategory.Qh.obj K)
  obtain ⟨f, hf⟩ := (J.property.map_bijective_of_isTriangulated DerivedCategory.Qh
    K).surjective
      (E.counitIso.inv.app (DerivedCategory.Qh.obj K))
  refine ⟨J, f, ?_⟩
  rw [Functor.comp_map, hf]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem canonical_adjunction_unit_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R) :
    NatTrans.CommShift adj.mapDerivedCategoryRightDerivedAdjunction.unit ℤ := by
  have : NatTrans.CommShift R.rightDerivedFunctorUnit ℤ := canonical_unit_commShift R
  have hunit : NatTrans.CommShift (adj.mapHomologicalComplex (.up ℤ)).unit ℤ := by
    constructor
    intro n
    ext K i
    dsimp [Adjunction.mapHomologicalComplex]
    simp only [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_id_hom_app,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
    simp only [HomologicalComplex.id_f, CochainComplex.shiftFunctor_obj_X', Category.id_comp,
      Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id]
    erw [Category.comp_id]
  have : NatTrans.CommShift (adj.mapHomotopyCategory (.up ℤ)).unit ℤ := by
    have heq : Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
        (adj.mapHomotopyCategory (.up ℤ)).unit =
        (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
          Functor.whiskerRight (adj.mapHomologicalComplex (.up ℤ)).unit
            (HomotopyCategory.quotient C (.up ℤ)) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (L.mapHomologicalComplex (.up ℤ))
            (R.mapHomotopyCategoryFactors (.up ℤ)).inv ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (L.mapHomotopyCategoryFactors (.up ℤ)).inv
            (R.mapHomotopyCategory (.up ℤ)) ≫
          (Functor.associator _ _ _).hom := by
      ext K
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
        Adjunction.mapHomotopyCategory_unit_app_quotient, Category.id_comp]
      simp [Functor.mapHomotopyCategoryFactors]
    have : NatTrans.CommShift (Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
        (adj.mapHomotopyCategory (.up ℤ)).unit) ℤ := by
      rw [heq]
      infer_instance
    exact NatTrans.CommShift.of_whiskerLeft _ (HomotopyCategory.quotient C (.up ℤ))
      (fun X ↦ ⟨_, 𝟙 _, (HomotopyCategory.quotient_obj_surjective X).choose_spec ▸
        inferInstance⟩)
  let η := adj.mapDerivedCategoryRightDerivedAdjunction.unit
  have heq : Functor.whiskerLeft DerivedCategory.Qh η =
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (adj.mapHomotopyCategory (.up ℤ)).unit DerivedCategory.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (L.mapHomotopyCategory (.up ℤ)) R.rightDerivedFunctorUnit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight L.mapDerivedCategoryFactorsh.inv R.rightDerivedFunctor ≫
        (Functor.associator _ _ _).hom := by
    ext K
    apply (cancel_mono (R.rightDerivedFunctor.map
      (L.mapDerivedCategoryFactorsh.hom.app K))).1
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Category.id_comp,
      Category.assoc, ← R.rightDerivedFunctor.map_comp,
      L.mapDerivedCategoryFactorsh.inv_hom_id_app, R.rightDerivedFunctor.map_id,
      Category.comp_id]
    erw [Category.id_comp, Category.comp_id]
    exact (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit K
  have : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Qh η) ℤ := by
    rw [heq]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Qh
    (fun X ↦ ⟨_, (DerivedCategory.Qh.objObjPreimageIso X).inv, inferInstance⟩)

private theorem operationDerivedAdjunction {C D : Type (u + 1)}
    [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} {R : Sheaf J CommRingCat.{u + 1}}
    {S : Sheaf K CommRingCat.{u + 1}} (o : Operation F R S) :
    o.DerivedAdjunction := by
  let := o.kInjectives
  have hu : NatTrans.CommShift o.derivedAdjunction.unit ℤ :=
    canonical_adjunction_unit_commShift o.moduleAdjunction
  have : o.derivedAdjunction.CommShift ℤ := Adjunction.CommShift.mk' _ _ hu
  refine ⟨(show NatTrans.CommShift o.derivedAdjunction.counit ℤ from inferInstance), ?_⟩
  intro I _
  have h := (o.moduleAdjunction.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso (Mod S) (.up ℤ))
    o.pullback.mapDerivedCategoryFactorsh.hom o.pushforward.rightDerivedFunctorUnit
    ((HomotopyCategory.quotient (Mod S) (.up ℤ)).obj I)
  dsimp only [Operation.rightComparison, Operation.derivedCounit, Operation.derivedAdjunction,
    Operation.left, Operation.right, Operation.leftModel, derivedPushforwardComplexComparison]
  simp only [Functor.map_comp, Category.assoc]
  have hn := o.moduleAdjunction.mapDerivedCategoryRightDerivedAdjunction.counit.naturality
    ((DerivedCategory.quotientCompQhIso (Mod S)).hom.app I)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  erw [reassoc_of% h]
  have hnf := o.pullback.mapDerivedCategoryFactorsh.hom.naturality
    ((o.pushforward.mapHomotopyCategoryFactors (.up ℤ)).inv.app I)
  dsimp only [Functor.comp_map] at hnf
  rw [reassoc_of% hnf]
  rw [o.pullback.mapDerivedCategoryFactorsh_hom_app]
  simp only [Category.assoc]
  simp [Adjunction.mapHomotopyCategory_counit_app_quotient,
    Functor.mapHomotopyCategoryFactors]

private theorem tensorModelWithShifts_nonempty {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u + 1}) :
    ∃ a : TensorModel R, Nonempty (TensorShifts a) := by
  obtain ⟨r, hr, _, hd⟩ := SheafOfModules.cochain_tensor_model_rigidity J R
  let a : TensorModel R := {
    preadditive := SheafOfModules.cochainModulesPreadditive R
    functor := SheafOfModules.siteDerivedTensorIndependentCoefficients J R
    representative := r
    descent := fun F G ↦ hd _ inferInstance F G }
  let stable : ∀ (P : CochainComplex (Mod R) ℤ),
      TensorFlatRepresentative (J := J) (R := R) P →
      ∀ n : ℤ, TensorFlatRepresentative (J := J) (R := R) (P⟦n⟧) :=
    fun P hp n ↦ (total_tensor_integer_shift_models.{u + 1, u, 0} J R).1 P hp.1 hp.2 n
  obtain ⟨s, hs, _, _⟩ := SheafOfModules.derived_tensor_shift_descent stable
  let := s
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.cochainModulesPreadditive R
  have hrep (P Q : CochainComplex (Mod R) ℤ)
      (hp : resolving R P) (hq : resolving R Q) :
      a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) =
        (tensorDescentPair P Q hp hq).hom := by
    exact hr _
  refine ⟨a, ⟨{
    shifts := s
    tensorAdditive := inferInstance
    tensorObjAdditive := fun _ ↦ inferInstance
    first := ?_
    second := ?_ }⟩⟩
  · intro P Q hp hq n
    refine ⟨stable P hp n, ?_⟩
    have h := (hs P Q hp hq n).1
    have h' := congrArg (fun f ↦ f ≫ (shiftFunctor (Der R) n).map
      (a.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩))) h
    change _ = _ at h'
    rw [← hrep P Q hp hq, ← hrep (P⟦n⟧) Q (stable P hp n) hq] at h'
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at h'
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at h'
    simpa only [a, siteRestrictionDerivedTensor, Functor.curry_obj_obj_map,
      Functor.curry_obj_map_app, Functor.flip_obj_map,
      SiteTensorComplexFunctor, SheafOfModules.tensorShiftTotal, total, tensor,
      Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
      ObjectProperty.ι_obj] using h'
  · intro P Q hp hq n
    refine ⟨stable Q hq n, ?_⟩
    have h := (hs P Q hp hq n).2
    have h' := congrArg (fun f ↦ f ≫ (shiftFunctor (Der R) n).map
      (a.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩))) h
    change _ = _ at h'
    rw [← hrep P Q hp hq, ← hrep P (Q⟦n⟧) hp (stable Q hq n)] at h'
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at h'
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at h'
    simpa only [a, siteRestrictionDerivedTensor, Functor.curry_obj_obj_map,
      Functor.curry_obj_map_app, Functor.flip_obj_map,
      SiteTensorComplexFunctor, SheafOfModules.tensorShiftTotal, total, tensor,
      Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
      ObjectProperty.ι_obj] using h'

private def globalOperation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X) :
    Operation (proEtaleBaseChange f) R_Y R_X := by
  let a := proEtaleRingDirectImageMap f R_Y R_X c
  let coeff :=
    (⟨Functor.whiskerRight a.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ :
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) ⟶
        ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology X)).obj
          ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X))
  let adj := proEtaleRingModuleAdjunction f R_Y R_X c
  have hright : (SheafOfModules.pushforward.{u + 1} coeff).IsRightAdjoint :=
    adj.isRightAdjoint
  let adj' := SheafOfModules.pullbackPushforwardAdjunction coeff
  have hpush : (SheafOfModules.pushforward.{u + 1} coeff).Additive :=
    inferInstanceAs (proEtaleRingModuleDirectImage f R_Y R_X c).Additive
  have hpull : (SheafOfModules.pullback.{u + 1} coeff).Additive :=
    adj'.left_adjoint_additive
  have hpullLim : PreservesFiniteLimits (SheafOfModules.pullback.{u + 1} coeff) :=
    preservesFiniteLimits_of_natIso (adj.leftAdjointUniq adj')
  have hpullColim : PreservesFiniteColimits (SheafOfModules.pullback.{u + 1} coeff) :=
    preservesFiniteColimits_of_natIso (adj.leftAdjointUniq adj')
  exact {
    continuous := inferInstance
    coefficient := coeff
    rightAdjoint := hright
    pullbackAdditive := hpull
    pushforwardAdditive := hpush
    pullbackLimits := hpullLim
    pullbackColimits := hpullColim
    kInjectives := inferInstance }

private def globalOrdinaryTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    (globalOperation f R S c).OrdinaryTensor := by
  let o := globalOperation f R S c
  let adj := proEtaleRingModuleAdjunction f R S c
  let e := o.moduleAdjunction.leftAdjointUniq adj
  let m := proEtaleOrdinaryTensorPullback f R S c
  refine {
    iso := fun M N ↦ e.app _ ≪≫ m M N ≪≫
      ((tensor S).mapIso (e.app M).symm).app _ ≪≫
        ((tensor S).obj (o.pullback.obj M)).mapIso (e.app N).symm
    pure_unit := ?_ }
  intro M N W x y
  have he (A : Mod R) : o.moduleAdjunction.unit.app A ≫
      o.pushforward.map (e.hom.app A) = adj.unit.app A :=
    o.moduleAdjunction.unit_leftAdjointUniq_hom_app adj A
  have hp := (Classical.choose_spec
    (proEtaleOrdinaryTensorPullback_existsUnique f R S c).exists).2 M N W.unop x y
  have hev (A : Mod R) (z : A.val.obj W) :
      (e.hom.app A).val.app ((proEtaleBaseChange f).op.obj W)
        ((o.moduleAdjunction.unit.app A).val.app W z) =
          (adj.unit.app A).val.app W z := by
    exact congrArg (fun k ↦ k.val.app W z) (he A)
  have hinv (A : Mod R) (z : A.val.obj W) :
      (e.inv.app A).val.app ((proEtaleBaseChange f).op.obj W)
        ((adj.unit.app A).val.app W z) =
          (o.moduleAdjunction.unit.app A).val.app W z := by
    rw [← hev A z]
    exact congrArg (fun k ↦ k.val.app ((proEtaleBaseChange f).op.obj W)
      ((o.moduleAdjunction.unit.app A).val.app W z)) (e.hom_inv_id_app A)
  change (((tensor S).map (e.inv.app M)).app _ ≫
      ((tensor S).obj (o.pullback.obj M)).map (e.inv.app N)).val.app
        ((proEtaleBaseChange f).op.obj W)
    ((m M N).hom.val.app ((proEtaleBaseChange f).op.obj W)
      ((e.hom.app _).val.app ((proEtaleBaseChange f).op.obj W)
        ((o.moduleAdjunction.unit.app _).val.app W (pure R M N W x y)))) = _
  rw [hev]
  change (m M N).hom.val.app ((proEtaleBaseChange f).op.obj W)
      ((adj.unit.app _).val.app W (pure R M N W x y)) =
    pure S _ _ ((proEtaleBaseChange f).op.obj W)
      ((adj.unit.app M).val.app W x) ((adj.unit.app N).val.app W y) at hp
  rw [hp]
  have ht := SheafOfModules.CochainScalarConstruction.pure_map S
    (e.inv.app M) (e.inv.app N) ((proEtaleBaseChange f).op.obj W)
    ((adj.unit.app M).val.app W x) ((adj.unit.app N).val.app W y)
  change _ = pure S _ _ _ _ _ at ht
  rw [hinv, hinv] at ht
  exact ht

/-- The canonically normalized global operations, tensor models and their shifts exist. -/
theorem globalModel_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X) :
    Nonempty (Global f R_Y R_X c) := by
  classical
  let o := globalOperation f R_Y R_X c
  obtain ⟨a, ⟨sa⟩⟩ := tensorModelWithShifts_nonempty R_Y
  obtain ⟨b, ⟨sb⟩⟩ := tensorModelWithShifts_nonempty R_X
  let mu := globalOrdinaryTensor f R_Y R_X c
  obtain ⟨t, ht⟩ := globalTensorComparison_exists f R_Y R_X c o rfl a b sa sb mu
  exact ⟨{
    operation := o
    coefficient_eq := rfl
    recordedDirectImage := rfl
    adjunction := operationDerivedAdjunction o
    tensorY := a
    tensorX := b
    tensorYShifts := sa
    tensorXShifts := sb
    ordinaryTensor := mu
    tensorComparison := t
    tensorComparison_shifts := ht }⟩

end AlgebraicGeometry.Scheme.ProjectionRestriction
