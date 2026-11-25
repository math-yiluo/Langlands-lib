/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
import WeilConjectures.Algebra.Homology.RingedSitePullback.PullbackLocalizationOfUniverses
import all WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLinePullbackTensor
import all WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLinePullbackFiniteLimits
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! Ordinary localized pullback and preservation of resolving complexes.

## References

* Stacks Project, Modules on Sites, Tag 04J0
* Cohomology on Sites, Tags 0G7E and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.ProjectionRestriction

open CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction

section SetLocalization
variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [HasFiniteLimits C] [HasFiniteLimits D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (U : C ⥤ D) [U.IsContinuous J K] [PreservesFiniteLimits U] (V : C)
  [(Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V))]

private def setRestrictionAdj (H : GrothendieckTopology C) (W : C) :=
  (Over.forgetAdjStar W).sheafPushforwardContinuous (E := Type (u + 1)) (H.over W) H

private theorem setRestrictionAdj_unit (A : Sheaf J (Type (u + 1)))
    (T : Cᵒᵖ) (x : A.obj.obj T) :
    ((setRestrictionAdj J V).unit.app A).hom.app T x =
      A.obj.map prod.snd.op x := by
  change A.obj.map ((Over.forgetAdjStar V).counit.app T.unop).op x = _
  rw [Over.forgetAdjStar_counit_app]
  rfl

private def setLocalRightIso :
    (Over.post (X := V) U).sheafPushforwardContinuous (Type (u + 1))
        (J.over V) (K.over (U.obj V)) ⋙
      (Over.star V).sheafPushforwardContinuous (Type (u + 1)) J (J.over V) ≅
    (Over.star (U.obj V)).sheafPushforwardContinuous (Type (u + 1)) K
        (K.over (U.obj V)) ⋙ U.sheafPushforwardContinuous (Type (u + 1)) J K := by
  let := Functor.isContinuous_comp U (Over.star (U.obj V)) J K (K.over (U.obj V))
  exact Functor.sheafPushforwardContinuousComp'
      (SheafOfModules.RingedSitePullback.starPostIso (U := U) V)
      (Type (u + 1)) J (J.over V) (K.over (U.obj V)) ≪≫
    (Functor.sheafPushforwardContinuousComp U (Over.star (U.obj V))
      (Type (u + 1)) J K (K.over (U.obj V))).symm

-- Compare the composite right adjoints through the product comparison.
private def setLocalLeftIso :
    J.overPullback (Type (u + 1)) V ⋙
        sheafPullback (Over.post U) (Type (u + 1)) (J.over V) (K.over (U.obj V)) ≅
      sheafPullback U (Type (u + 1)) J K ⋙
        K.overPullback (Type (u + 1)) (U.obj V) :=
  Adjunction.leftAdjointUniq
    ((setRestrictionAdj J V).comp
      (sheafAdjunctionContinuous (Over.post U) (Type (u + 1))
        (J.over V) (K.over (U.obj V))))
    (((sheafAdjunctionContinuous U (Type (u + 1)) J K).comp
      (setRestrictionAdj K (U.obj V))).ofNatIsoRight (setLocalRightIso J K U V).symm)

private theorem setLocalLeftIso_unit (A : Sheaf J (Type (u + 1))) :
    (sheafAdjunctionContinuous (Over.post U) (Type (u + 1))
        (J.over V) (K.over (U.obj V))).unit.app (A.over V) ≫
      ((Over.post U).sheafPushforwardContinuous (Type (u + 1))
        (J.over V) (K.over (U.obj V))).map ((setLocalLeftIso J K U V).hom.app A) =
    (J.overPullback (Type (u + 1)) V).map
      ((sheafAdjunctionContinuous U (Type (u + 1)) J K).unit.app A) := by
  let av := sheafAdjunctionContinuous (Over.post U) (Type (u + 1))
    (J.over V) (K.over (U.obj V))
  let a := sheafAdjunctionContinuous U (Type (u + 1)) J K
  let a₁ := (setRestrictionAdj J V).comp av
  let a₂ := (a.comp (setRestrictionAdj K (U.obj V))).ofNatIsoRight
    (setLocalRightIso J K U V).symm
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app a₁ a₂ A
  change (setRestrictionAdj J V).homEquiv _ _
    (av.homEquiv _ _ ((setLocalLeftIso J K U V).hom.app A)) = _ at h
  apply (setRestrictionAdj J V).homEquiv _ _ |>.injective
  change (setRestrictionAdj J V).homEquiv _ _
    (av.homEquiv _ _ ((setLocalLeftIso J K U V).hom.app A)) = _
  rw [h]
  rw [Adjunction.homEquiv_unit]
  change ((a.comp (setRestrictionAdj K (U.obj V))).unit.app A) ≫
    (setLocalRightIso J K U V).inv.app _ = _
  rw [Adjunction.comp_unit_app]
  ext X x
  change ((setLocalRightIso J K U V).inv.app
      (((sheafPullback U (Type (u + 1)) J K).obj A).over (U.obj V))).hom.app X
      (((setRestrictionAdj K (U.obj V)).unit.app
        ((sheafPullback U (Type (u + 1)) J K).obj A)).hom.app (U.op.obj X)
          ((a.unit.app A).hom.app X x)) =
    (a.unit.app A).hom.app (op (V ⨯ X.unop))
      (((setRestrictionAdj J V).unit.app A).hom.app X x)
  rw [setRestrictionAdj_unit, setRestrictionAdj_unit]
  change (((sheafPullback U (Type (u + 1)) J K).obj A).obj.map
      (prodComparison U V X.unop).op)
      ((((sheafPullback U (Type (u + 1)) J K).obj A).obj.map prod.snd.op)
        ((a.unit.app A).hom.app X x)) = _
  rw [← Functor.map_comp_apply, ← op_comp, prodComparison_snd]
  exact ((a.unit.app A).hom.naturality_apply (prod.snd : V ⨯ X.unop ⟶ X.unop).op x).symm

-- The comparison carries the local unit to the restriction of the global unit.
private def localizeSetPresentation
    {A : Sheaf J (Type (u + 1))} {B : Sheaf K (Type (u + 1))}
    (p : CategoryTheory.SignedLinePullbackConstruction.SheafPullbackUnitPresentation.{u + 1, u, 0}
      (F := U) A B) :
    CategoryTheory.SignedLinePullbackConstruction.SheafPullbackUnitPresentation.{u + 1, u, 0}
      (F := Over.post (X := V) U) (A.over V) (B.over (U.obj V)) where
  unit := ⟨{ app T := p.unit.hom.app (op T.unop.left)
             naturality _ _ f := p.unit.hom.naturality ((Over.forget V).op.map f) }⟩
  iso := (K.overPullback (Type (u + 1)) (U.obj V)).mapIso p.iso ≪≫
    ((setLocalLeftIso J K U V).app A).symm
  equation := by
    intro T x
    have h := congrArg (fun k ↦ k.hom.app T x) (setLocalLeftIso_unit J K U V A)
    change ((setLocalLeftIso J K U V).hom.app A).hom.app ((Over.post U).op.obj T)
      (((sheafAdjunctionContinuous (Over.post U) (Type (u + 1))
        (J.over V) (K.over (U.obj V))).unit.app (A.over V)).hom.app T x) =
      ((sheafAdjunctionContinuous U (Type (u + 1)) J K).unit.app A).hom.app
        (op T.unop.left) x at h
    change ((setLocalLeftIso J K U V).inv.app A).hom.app ((Over.post U).op.obj T)
      (p.iso.hom.hom.app (U.op.obj (op T.unop.left))
        (p.unit.hom.app (op T.unop.left) x)) = _
    rw [p.equation, ← h]
    exact congrArg (fun k ↦ k.hom.app ((Over.post U).op.obj T)
      (((sheafAdjunctionContinuous (Over.post U) (Type (u + 1))
        (J.over V) (K.over (U.obj V))).unit.app (A.over V)).hom.app T x))
      ((setLocalLeftIso J K U V).hom_inv_id_app A)

end SetLocalization

section FromPresentation
variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [HasFiniteLimits C] [HasFiniteLimits D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K] [PreservesFiniteLimits U]
  {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}

open SheafOfModules
open SheafOfModules.SignedLineDerivedBaseChange
open CategoryTheory.SignedLinePullbackConstruction

private theorem operationOfPresentation
    (a : (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R ⟶
      (U.sheafPushforwardContinuous RingCat.{u + 1} J K).obj
        ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (p : CategoryTheory.SignedLinePullbackConstruction.SheafPullbackUnitPresentation.{u + 1, u, 0}
      (F := U)
      ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj R)
      ((sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).obj S))
    (hp : p.unit = (sheafCompose J (CategoryTheory.forget RingCat.{u + 1})).map a) :
    ∃ o : Operation U R S, o.coefficient = a ∧
      ∃ _mu : o.OrdinaryTensor, ∀ P, resolving R P →
        resolving S ((o.pullback.mapHomologicalComplex (.up ℤ)).obj P) := by
  let hm := module_pushforward_isRightAdjoint_of_universes.{u + 1, u, 0} a
  let := hm
  let : RepresentablyFlat U := flat_of_preservesFiniteLimits U
  let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  let : AB5OfSize.{u, u + 1} AddCommGrpCat.{u + 1} :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  obtain ⟨hJ, _⟩ := coefficientSheafification.{u + 1, u, u + 1} J
  obtain ⟨hK, hKW⟩ := coefficientSheafification.{u + 1, u, u + 1} K
  let := hJ
  let := hK
  let := hKW
  let : K.PreservesSheafification (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    (ringSheafification.{u + 1, u, u + 1} K).2.2
  let : PreservesFilteredColimitsOfSize.{u, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1} _
  let : ∀ W : Dᵒᵖ, PreservesColimitsOfShape (CostructuredArrow U.op W)
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) := fun _ ↦ inferInstance
  obtain ⟨e, he⟩ :=
    SignedLinePullbackConstruction.inverseImage_underlying_of_ring_presentation.{u + 1, u, 0} a p hp
  let ea :=
    CategoryTheory.SignedLinePullbackConstruction.sheafPullbackForgetIso.{u + 1, u, 0, u + 2}
    J K U (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let em := Functor.isoWhiskerRight e
      (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u + 1})) ≪≫
    Functor.isoWhiskerLeft (toSheaf _) ea
  have hem (M : Mod R) (W : Cᵒᵖ) (x : M.val.obj W) :
      (em.hom.app M).hom.app (U.op.obj W)
        (ringedSitePullbackSection.{u + 1, u, 0} a
          hm
          M W.unop x) =
      ((sheafAdjunctionContinuous U (Type (u + 1)) J K).unit.app
        ((toSheaf _ ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj M)).hom.app W x := by
    have h := congrArg (fun f ↦ f.hom.app W x) (he M)
    change (e.hom.app M).hom.app (U.op.obj W)
      (ringedSitePullbackSection.{u + 1, u, 0} a
          hm
        M W.unop x) = _ at h
    change (ea.hom.app ((toSheaf _).obj M)).hom.app (U.op.obj W)
      ((e.hom.app M).hom.app (U.op.obj W) _) = _
    rw [h]
    have hu :=
      sheafPullbackForgetIso_unit.{u + 1, u, 0, u + 2}
        J K U (CategoryTheory.forget AddCommGrpCat.{u + 1}) ((toSheaf _).obj M)
    exact congrArg (fun f ↦ f.hom.app W x) hu
  obtain ⟨I, hI, _, hMI⟩ := algebraic_pullback_of_presentations.{u + 1, u, 0} a p hp em hem
  let : (pushforward.{u + 1} a).Additive := { map_add := rfl }
  let : (pull.{u + 1, u, 0} a).Additive := (pullbackPushforwardAdjunction a).left_adjoint_additive
  let : PreservesFiniteLimits (pull.{u + 1, u, 0} a ⋙ toSheaf _) :=
    preservesFiniteLimits_of_natIso e.symm
  let : PreservesFiniteLimits (pull.{u + 1, u, 0} a) :=
    preservesFiniteLimits_of_reflects_of_preserves (pull.{u + 1, u, 0} a) (toSheaf _)
  let : IsGrothendieckAbelian.{u + 1} (Mod S) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
      K S).1
  let : Abelian.HasKInjectiveResolutions (Mod S) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  let o : Operation U R S := { coefficient := a }
  obtain ⟨k, _, hk⟩ := inverse_tensor_source_unit.{u + 1, u, 0} a em hem I hI hMI
  let mu : o.OrdinaryTensor :=
    { iso := k
      pure_unit := fun M N W x y ↦ hk M N W.unop x y }
  refine ⟨o, rfl, mu, ?_⟩
  intro P hP
  let : I.modules.Additive := by rw [hI]; infer_instance
  let A : SystemScalarModel.{u + 1, u, u + 1} (𝟙 S) := (nonempty_systemScalarModel (𝟙 S)).some
  let F := I.modules
  have ht := isKFlat_ringedToposPullback
    (sheafPullback U (Type (u + 1)) J K)
    (U.sheafPushforwardContinuous (Type (u + 1)) J K)
    (sheafAdjunctionContinuous U (Type (u + 1)) J K) I (𝟙 S)
    (F ⋙ A.model.E) (fun M ↦ A.model.obj_eq (F.obj M))
    (fun f ↦ A.model.map_eq (F.map f)) P hP.1 hP.2
  let ec := (NatIso.mapHomologicalComplex
    (Functor.isoWhiskerLeft F (systemScalarModelUnit rfl A) ≪≫ F.rightUnitor)
    (.up ℤ)).app P
  have hr : resolving S ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
    ⟨kFlat_iso_independent S ec ht.1, fun n ↦
      flatOnSite_of_iso S ((HomologicalComplex.eval _ (.up ℤ) n).mapIso ec) (ht.2 n)⟩
  simpa only [F, hI] using hr

end FromPresentation

set_option linter.unusedVariables false in
/-- Localization of the ordinary exact module pullback preserves resolving complexes. -/
theorem localOrdinaryResolving_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)
    (g : Global f R_Y R_X c) (V : Y.ProEt) :
    ∃ o : Operation (Over.post (X := V) (proEtaleBaseChange f)) (R_Y.over V)
        (R_X.over ((proEtaleBaseChange f).obj V)),
      (∀ T : Over V, o.coefficient.hom.app (op T) =
        g.operation.coefficient.hom.app (op T.left)) ∧
      ∃ mu : o.OrdinaryTensor,
        ∀ P, resolving (R_Y.over V) P →
          resolving (R_X.over ((proEtaleBaseChange f).obj V))
            ((o.pullback.mapHomologicalComplex (.up ℤ)).obj P) := by
  let U := proEtaleBaseChange f
  let J := ProEt.topology Y
  let K := ProEt.topology X
  let : (Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V)) :=
    SheafOfModules.RingedSitePullback.local_continuous
      (proEtaleBaseChangeCoverPreserving f) V
  obtain ⟨e, he, _⟩ := ProEtaleTensorComparison.ringSetsIdentification_exists f R_Y
  let q := e ≪≫ (sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).mapIso c
  have hq (W : Y.ProEt) (r : R_Y.obj.obj (op W)) :
      q.hom.hom.app (op (U.obj W))
        (((sheafAdjunctionContinuous U (Type (u + 1)) J K).unit.app
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj R_Y)).hom.app
            (op W) r) = g.operation.coefficient.hom.app (op W) r := by
    change c.hom.hom.app (op (U.obj W))
      (e.hom.hom.app (op (U.obj W)) _) = _
    have h := he W r
    change e.hom.hom.app (op (U.obj W))
      (((sheafAdjunctionContinuous U (Type (u + 1)) J K).unit.app
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj R_Y)).hom.app
          (op W) r) = _ at h
    rw [h, g.coefficient_eq]
    rfl
  let p : CategoryTheory.SignedLinePullbackConstruction.SheafPullbackUnitPresentation.{u + 1, u, 0}
      (F := U)
      ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj R_Y)
      ((sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).obj R_X) :=
    { unit := (sheafCompose J (CategoryTheory.forget RingCat.{u + 1})).map g.operation.coefficient
      iso := q.symm
      equation := by
        intro W x
        change q.inv.hom.app (U.op.obj W)
          (g.operation.coefficient.hom.app W x) = _
        rw [← hq W.unop x]
        exact congrArg (fun k ↦ k.hom.app (U.op.obj W)
          (((sheafAdjunctionContinuous U (Type (u + 1)) J K).unit.app
            ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj R_Y)).hom.app W x))
          q.hom_inv_id }
  let a := SheafOfModules.RingedSitePullback.locMap.{u + 1, u, 0} g.operation.coefficient V
  let pv := localizeSetPresentation J K U V p
  have hpv : pv.unit = (sheafCompose (J.over V)
      (CategoryTheory.forget RingCat.{u + 1})).map a := rfl
  obtain ⟨o, ho, mu, hmu⟩ := operationOfPresentation
    (J := J.over V) (K := K.over (U.obj V)) (U := Over.post (X := V) U)
    (R := R_Y.over V) (S := R_X.over (U.obj V)) a pv hpv
  refine ⟨o, ?_, mu, hmu⟩
  intro T
  rw [ho]
  rfl

end AlgebraicGeometry.Scheme.ProjectionRestriction
