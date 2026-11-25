/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCoefficientLayerData
public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerTensorComplex
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement

import WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
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
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import all WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCoefficientLayerTriangleCore
import all WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientModelResidueComparison
import all WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerTensorModelHomologyIdentification
import WeilConjectures.CategoryTheory.ConstantModuleFlat
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerKernelConstantComparison
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerOrdinaryTensorComparison

/-! # Derived slice comparison for the finite quotient layer

Source: Stacks Project, sites-cohomology.tex, Tags 094I and 06YU.
(blueprint: lem-weil-pbc-finite-quotient-layer-tensor-derived-slice-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local irreducible] completedAdicChangeData HasDerivedCategory.standard
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.siteDerivedTensorIndependentCoefficients

private abbrev layerModules (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}) :=
  SheafOfModules.{t + 1} ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)

private abbrev layerRes (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :=
  SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map f)

private instance layerRes_limits (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    PreservesFiniteLimits (layerRes X f) := by
  let G := SheafOfModules.toSheaf.{t + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
  have : PreservesFiniteLimits (layerRes X f ⋙ G) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)))
  exact preservesFiniteLimits_of_reflects_of_preserves (layerRes X f) G

private instance layerRes_colimits (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    PreservesFiniteColimits (layerRes X f) := by
  let G := SheafOfModules.toSheaf.{t + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
  have : PreservesFiniteColimits (layerRes X f ⋙ G) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)))
  exact preservesFiniteColimits_of_reflects_of_preserves (layerRes X f) G

private def layerTensor (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}) (N : layerModules X R) :
    DerivedCategory (layerModules X R) ⥤ DerivedCategory (layerModules X R) :=
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  (𝟭 _).prod' ((Functor.const _).obj ((DerivedCategory.singleFunctor _ 0).obj N)) ⋙
    SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X) R

-- Ordinary balancing is natural in the complex term that will be resolved below.
private theorem layerCancellation (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (f : R ⟶ S) (N : layerModules X S) :
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.monoidalCategory S
    Nonempty (MonoidalCategory.tensorRight ((layerRes X f).obj N) ≅
      completedAdicChange X f ⋙ MonoidalCategory.tensorRight N ⋙ layerRes X f) := by
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.symmetricCategory S
  let E := completedAdicChange X f
  have hobj : ∀ M, E.obj M = SheafOfModules.changeOfRings f M := completedChange_obj X f
  have hm : ∀ {M M'} (g : M ⟶ M'), E.map g = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom f M g ≫ eqToHom (hobj M').symm :=
    fun g ↦ completedChange_map X f g
  change Nonempty (tensorRight ((layerRes X f).obj N) ≅
    E ⋙ tensorRight N ⋙ layerRes X f)
  clear_value E
  obtain ⟨e, he⟩ :=
    SheafOfModules.exists_changeOfRings_tensorCancellation_independentCoefficients f
  let a (M : layerModules X R) :
      (layerRes X f).obj (N ⊗ E.obj M) ≅ (layerRes X f).obj N ⊗ M :=
    (layerRes X f).mapIso
      ((MonoidalCategory.curriedTensor _).obj N |>.mapIso
        (eqToIso (hobj M))) ≪≫ e N M
  let c : E ⋙ MonoidalCategory.tensorLeft N ⋙ layerRes X f ≅
      MonoidalCategory.tensorLeft ((layerRes X f).obj N) :=
    NatIso.ofComponents a (by
      intro M M' g
      have hs : whiskerLeft N (E.map g) ≫ whiskerLeft N (eqToHom (hobj M')) =
          whiskerLeft N (eqToHom (hobj M)) ≫
            whiskerLeft N (SheafOfModules.changeOfRingsHom f M g) := by
        change (tensorLeft N).map (E.map g) ≫ (tensorLeft N).map _ =
          (tensorLeft N).map _ ≫ (tensorLeft N).map _
        rw [← Functor.map_comp, ← Functor.map_comp, hm]
        simp only [Category.assoc, eqToHom_trans, eqToHom_refl,
          Category.comp_id]
      change (layerRes X f).map (whiskerLeft N (E.map g)) ≫
          ((layerRes X f).map (whiskerLeft N (eqToHom (hobj M'))) ≫ (e N M').hom) =
        ((layerRes X f).map (whiskerLeft N (eqToHom (hobj M))) ≫ (e N M).hom) ≫
          whiskerLeft ((layerRes X f).obj N) g
      rw [← Category.assoc, ← Functor.map_comp, hs, Functor.map_comp, Category.assoc]
      have hh := he (𝟙 N) g
      rw [(layerRes X f).map_id, id_tensorHom, id_tensorHom] at hh
      simpa only [Category.assoc] using
        congrArg ((layerRes X f).map (whiskerLeft N (eqToHom (hobj M))) ≫ ·) hh)
  exact ⟨(BraidedCategory.tensorLeftIsoTensorRight ((layerRes X f).obj N)).symm ≪≫
    c.symm ≪≫ Functor.isoWhiskerLeft E
      (Functor.isoWhiskerRight (BraidedCategory.tensorLeftIsoTensorRight N) (layerRes X f))⟩

-- Resolve only the first factor; the second factor can be any residue module.
private theorem layerProjection (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (f : R ⟶ S) (K : DerivedCategory (layerModules X R)) (N : layerModules X S) :
    Nonempty ((layerTensor X R ((layerRes X f).obj N)).obj K ≅
      (layerRes X f).mapDerivedCategory.obj
        ((layerTensor X S N).obj ((completedAdicDerivedChange X f).obj K))) := by
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let G := DerivedCategory.Q.objPreimage K
  obtain ⟨P, q, hP, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) G
  have := hq
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let E := completedAdicChange X f
  let P' := (E.mapHomologicalComplex (.up ℤ)).obj P
  have hP' : CochainComplex.IsKFlatIndependentCoefficients (R := S) P' :=
    SheafOfModules.changeOfRings_isKFlat_independentCoefficients f P E
      ((completedAdicChangeData X f).choose_spec.choose)
      (fun g ↦ (completedAdicChangeData X f).choose_spec.choose_spec.choose g) hP
  obtain ⟨d⟩ := completedChange_modelIso X f P hP
  let e' : DerivedCategory.Q.obj P' ≅ (completedAdicDerivedChange X f).obj K :=
    d.symm ≪≫ (completedAdicDerivedChange X f).mapIso e
  obtain ⟨cR, _, _⟩ := SheafOfModules.ringed_kFlat_single_tensor_comparison R
  obtain ⟨cS, _, _⟩ := SheafOfModules.ringed_kFlat_single_tensor_comparison S
  let tS := MonoidalCategory.tensorRight N
  let tR := MonoidalCategory.tensorRight ((layerRes X f).obj N)
  obtain ⟨o⟩ := layerCancellation X f N
  let b : (tR.mapHomologicalComplex (.up ℤ)).obj P ≅
      ((layerRes X f).mapHomologicalComplex (.up ℤ)).obj
        ((tS.mapHomologicalComplex (.up ℤ)).obj P') :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ o.app (P.X i))
      (fun i j _ ↦ (o.hom.naturality (P.d i j)).symm)
  let sR := (DerivedCategory.singleFunctorIsoCompQ _ 0).app ((layerRes X f).obj N)
  let sS := (DerivedCategory.singleFunctorIsoCompQ _ 0).app N
  let T := SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X) R
  let T' := SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X) S
  exact ⟨(layerTensor X R ((layerRes X f).obj N)).mapIso e.symm ≪≫
    T.mapIso ((Iso.refl _).prod sR) ≪≫ cR P hP ((layerRes X f).obj N) ≪≫
    DerivedCategory.Q.mapIso b ≪≫
    ((layerRes X f).mapDerivedCategoryFactors.app _).symm ≪≫
    (layerRes X f).mapDerivedCategory.mapIso
      ((cS P' hP' N).symm ≪≫ T'.mapIso ((Iso.refl _).prod sS.symm) ≪≫
        (layerTensor X S N).mapIso e')⟩

private theorem layerSecond_id
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{t + 1}}
    [J.HasSheafCompose (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
    [HasWeakSheafify J AddCommGrpCat.{t + 1}]
    (F G : SheafOfModules.{t + 1}
      ((sheafCompose J (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) :
    SheafOfModules.siteSheafTensorSecondMap (A := R) F (𝟙 G) = 𝟙 _ := by
  have h : SheafOfModules.siteTensorSecondMap (A := R) F.val (𝟙 G : G ⟶ G).val = 𝟙 _ := by
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl
  unfold SheafOfModules.siteSheafTensorSecondMap
  rw [h]
  exact (PresheafOfModules.sheafification (R :=
    (sheafCompose J (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
    (𝟙 _)).map_id _

private theorem layerOrdinaryOver (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}) (U : X.ProEt)
    (N : layerModules X R) :
    let := SheafOfModules.monoidalCategory R
    let : MonoidalCategory (SheafOfModules.{t + 1}
      (((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R).over U)) :=
    SheafOfModules.monoidalCategory (R.over U)
    Nonempty (MonoidalCategory.tensorRight N ⋙ SheafOfModules.overFunctor _ U ≅
      SheafOfModules.overFunctor _ U ⋙ MonoidalCategory.tensorRight (N.over U)) := by
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.isMonoidal_W_independentCoefficients (R.over U)
  let := SheafOfModules.monoidalCategory R
  let : MonoidalCategory (SheafOfModules.{t + 1}
      (((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R).over U)) :=
    SheafOfModules.monoidalCategory (R.over U)
  let V := SheafOfModules.overFunctor.{t + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) U
  obtain ⟨e, he, _⟩ := SheafOfModules.exists_localizedSiteTensorRestriction
    (ProEt.topology X) R U
  let a : SheafOfModules.siteSheafTensorRight (A := R) N ⋙ V ≅
      V ⋙ SheafOfModules.siteSheafTensorRight (A := R.over U) (N.over U) :=
    NatIso.ofComponents (fun M ↦ e M N) (by
      intro M M' g
      have h := he M M' N N g (𝟙 N)
      rw [layerSecond_id, Category.comp_id] at h
      change _ = _ ≫ _ ≫ SheafOfModules.siteSheafTensorSecondMap
        (A := R.over U) (M'.over U) (𝟙 (N.over U)) at h
      rw [layerSecond_id, Category.comp_id] at h
      exact h)
  exact ⟨Functor.isoWhiskerRight (SheafOfModules.siteSheafTensorRightIso R N).symm V ≪≫
    a ≪≫ Functor.isoWhiskerLeft V
      (SheafOfModules.siteSheafTensorRightIso (R.over U) (N.over U))⟩

private local instance (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}) (U : X.ProEt)
    [h : HasDerivedCategory.{t + 2} (SheafOfModules.{t + 1}
      ((sheafCompose ((ProEt.topology X).over U)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (R.over U)))] :
    Category.{t + 2} (@DerivedCategory (SheafOfModules.{t + 1}
      (((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R).over U)) _ _ h) :=
  inferInstanceAs (Category.{t + 2} (DerivedCategory (SheafOfModules.{t + 1}
    ((sheafCompose ((ProEt.topology X).over U)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (R.over U)))))

private def layerSliceTensor (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}) (U : X.ProEt)
    (N : layerModules X R) :=
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  let S := (sheafCompose ((ProEt.topology X).over U)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (R.over U)
  (𝟭 _).prod' ((Functor.const _).obj
    ((DerivedCategory.singleFunctor (SheafOfModules.{t + 1} S) 0).obj (N.over U))) ⋙
    SheafOfModules.siteDerivedTensorIndependentCoefficients ((ProEt.topology X).over U)
      (R.over U)

-- Exact restriction carries a K-flat representative to a K-flat representative.
private theorem layerTensor_over (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}) (U : X.ProEt)
    (K : DerivedCategory (layerModules X R)) (N : layerModules X R) :
    Nonempty ((ringedDerivedRestrictionGeneral _ U).obj ((layerTensor X R N).obj K) ≅
      (layerSliceTensor X R U N).obj ((ringedDerivedRestrictionGeneral _ U).obj K)) := by
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  let := SheafOfModules.monoidalCategory R
  let : MonoidalCategory (SheafOfModules.{t + 1}
      (((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R).over U)) :=
    SheafOfModules.monoidalCategory (R.over U)
  let V := SheafOfModules.overFunctor.{t + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) U
  have := (ringedOverFunctor_exactGeneral
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) U).1
  have := (ringedOverFunctor_exactGeneral
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) U).2.1
  have := (ringedOverFunctor_exactGeneral
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) U).2.2
  let G := DerivedCategory.Q.objPreimage K
  obtain ⟨P, q, hP, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) G
  have := hq
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have : (tensorRight (N.over U)).PreservesZeroMorphisms := by
    change (tensorRight (show SheafOfModules.{t + 1}
      ((sheafCompose ((ProEt.topology X).over U)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (R.over U)) from
          N.over U)).PreservesZeroMorphisms
    have := SheafOfModules.tensorPreadditive (R.over U)
    infer_instance
  let P' := (V.mapHomologicalComplex (.up ℤ)).obj P
  have hP' : CochainComplex.IsKFlatIndependentCoefficients (R := R.over U) P' :=
    (SheafOfModules.ringedSite_restriction_exact_kflat.{t + 1, t, 0}
      (ProEt.topology X) R U).2.2 P hP
  obtain ⟨cR, _, _⟩ := SheafOfModules.ringed_kFlat_single_tensor_comparison R
  obtain ⟨cS, _, _⟩ := SheafOfModules.ringed_kFlat_single_tensor_comparison (R.over U)
  obtain ⟨o⟩ := layerOrdinaryOver X R U N
  let b : (V.mapHomologicalComplex (.up ℤ)).obj
      (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P) ≅
      ((tensorRight (N.over U)).mapHomologicalComplex (.up ℤ)).obj P' :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ o.app (P.X i))
      (fun i j _ ↦ (o.hom.naturality (P.d i j)).symm)
  let e' : DerivedCategory.Q.obj P' ≅ V.mapDerivedCategory.obj K :=
    (V.mapDerivedCategoryFactors.app P).symm ≪≫ V.mapDerivedCategory.mapIso e
  let sR := (DerivedCategory.singleFunctorIsoCompQ _ 0).app N
  let sS := (DerivedCategory.singleFunctorIsoCompQ _ 0).app (N.over U)
  let T := SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X) R
  let T' := SheafOfModules.siteDerivedTensorIndependentCoefficients
    ((ProEt.topology X).over U) (R.over U)
  exact ⟨V.mapDerivedCategory.mapIso
      ((layerTensor X R N).mapIso e.symm ≪≫
        T.mapIso ((Iso.refl _).prod sR) ≪≫ cR P hP N) ≪≫
    V.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso b ≪≫
    (cS P' hP' (N.over U)).symm ≪≫ T'.mapIso ((Iso.refl _).prod sS.symm) ≪≫
    (layerSliceTensor X R U N).mapIso e'⟩

private abbrev layerSliceRes (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :=
  SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose ((ProEt.topology X).over U)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        (((ProEt.topology X).overPullback CommRingCat.{t + 1} U).map f))

private instance layerSliceRes_limits (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    PreservesFiniteLimits (layerSliceRes X U f) :=
  (SheafOfModules.sheafRingDerivedCoefficientAdjunction
    (((ProEt.topology X).overPullback CommRingCat.{t + 1} U).map f)).choose

private instance layerSliceRes_colimits (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    PreservesFiniteColimits (layerSliceRes X U f) :=
  (SheafOfModules.sheafRingDerivedCoefficientAdjunction
    (((ProEt.topology X).overPullback CommRingCat.{t + 1} U).map f)).choose_spec.choose
private theorem layerRes_over (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    Nonempty ((layerRes X f).mapDerivedCategory ⋙ ringedDerivedRestrictionGeneral _ U ≅
      ringedDerivedRestrictionGeneral _ U ⋙ (layerSliceRes X U f).mapDerivedCategory) := by
  have := (ringedOverFunctor_exactGeneral
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) U).1
  have := (ringedOverFunctor_exactGeneral
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) U).2.1
  have := (ringedOverFunctor_exactGeneral
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) U).2.2
  have := (ringedOverFunctor_exactGeneral
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S) U).1
  have := (ringedOverFunctor_exactGeneral
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S) U).2.1
  have := (ringedOverFunctor_exactGeneral
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S) U).2.2
  have := layerSliceRes_limits X U f
  have := layerSliceRes_colimits X U f
  let e : layerRes X f ⋙ SheafOfModules.overFunctor _ U ≅
      SheafOfModules.overFunctor _ U ⋙ layerSliceRes X U f := Iso.refl _
  exact ⟨Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm⟩

private instance layerConstant_zero (X : Scheme.{t}) (B : Type t) [CommRing B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    {R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : adicConstantRing X B ⟶ R) :
    (finiteCoefficientConstantFunctor X B φ).PreservesZeroMorphisms := by
  unfold finiteCoefficientConstantFunctor
  infer_instance

private theorem layerConstantKFlat (X : Scheme.{t}) (B : Type t) [CommRing B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    {R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : adicConstantRing X B ⟶ R)
    (P : CochainComplex (ModuleCat.{t} B) ℤ) (b : ℤ) (hb : P.IsStrictlyLE b)
    (hp : ∀ i, Module.Projective B (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R)
      (((finiteCoefficientConstantFunctor X B φ).mapHomologicalComplex (.up ℤ)).obj P) := by
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  have := (baseConstantExact X B).1
  let C : CochainComplex (SheafOfModules (adicModuleRing X B)) ℤ :=
    finiteModelConstantComplex X B P
  have : C.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (baseConstantFunctor X B).map_isZero (P.isZero_of_isStrictlyLE b i hi)
  have hf (i : ℤ) : SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      (J := ProEt.topology X) (R := adicConstantRing X B) (C.X i) := by
    let L := ModuleCat.uliftFunctor.{t + 1, t} B ⋙
      ModuleCat.restrictScalars.{t + 1}
        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
    have := hp i
    have : Projective (P.X i) := inferInstance
    have : Projective (L.obj (P.X i)) := inferInstance
    have : Module.Projective (ULift.{t + 1} B) (L.obj (P.X i)) := inferInstance
    exact isFlatOnSite_constantModule (ProEt.topology X) (ULift.{t + 1} B)
      (L.obj (P.X i)) inferInstance
  have hk := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    (adicConstantRing X B) C b hf
  exact SheafOfModules.changeOfRings_isKFlat_independentCoefficients φ C
    (completedAdicChange X φ) (completedChange_obj X φ)
      (fun g ↦ completedChange_map X φ g) hk

-- The bounded projective chart can be evaluated using the ordinary comparison termwise.
private theorem layerChartComputation
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ k : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (k + 1))).PreservesZeroMorphisms]
    (φ : ∀ k, adicConstantRing X (A ⧸ d.ideal ^ (k + 1)) ⟶
      completedAdicFiniteCommRing X d k)
    (hφ : ∀ k, IsIso (φ k)) (hc : FinitePerfectModelsCompatible X d φ)
    (n : ℕ) (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (0 + 1))) ℤ)
    (b : ℤ) (hb : P.IsStrictlyLE b)
    (hp : ∀ i, Module.Projective (A ⧸ d.ideal ^ (0 + 1)) (P.X i)) :
    Nonempty ((layerRes X
      (completedAdicQuotientCommMap X d (n + 1) 0 (Nat.zero_le _))).mapDerivedCategory.obj
        ((layerTensor X (completedAdicFiniteCommRing X d 0)
          ((finiteCoefficientConstantFunctor X _ (φ 0)).obj
            (finiteQuotientLayerModule d.ideal n))).obj
          ((completedAdicDerivedChange X (φ 0)).obj
            (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P)))) ≅
      (completedAdicDerivedChange X (φ (n + 1))).obj
        (DerivedCategory.Q.obj (finiteModelConstantComplex X _
          (finiteQuotientLayerTensorComplex d.ideal n P)))) := by
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  have := hφ 0
  have := hφ (n + 1)
  let S := completedAdicFiniteCommRing X d 0
  let := SheafOfModules.monoidalCategory S
  let N := (finiteCoefficientConstantFunctor X _ (φ 0)).obj
    (finiteQuotientLayerModule d.ideal n)
  let C := finiteModelConstantComplex X _ P
  let C' := ((completedAdicChange X (φ 0)).mapHomologicalComplex (.up ℤ)).obj C
  let V := layerRes X (completedAdicQuotientCommMap X d (n + 1) 0 (Nat.zero_le _))
  have hk : CochainComplex.IsKFlatIndependentCoefficients (R := S) C' :=
    layerConstantKFlat X _ (φ 0) P b hb hp
  obtain ⟨o⟩ := finiteQuotient_layer_ordinary_tensor_comparison X d φ hφ hc n
  let q : (V.mapHomologicalComplex (.up ℤ)).obj
      (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj C') ≅
      ((finiteCoefficientConstantFunctor X _ (φ (n + 1))).mapHomologicalComplex
        (.up ℤ)).obj (finiteQuotientLayerTensorComplex d.ideal n P) :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ o.app (P.X i))
      (fun i j _ ↦ (o.hom.naturality (P.d i j)).symm)
  obtain ⟨c, _, _⟩ := SheafOfModules.ringed_kFlat_single_tensor_comparison S
  let T := SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X) S
  let a := derivedChangeComplexIso X (φ 0) C
  let s := (DerivedCategory.singleFunctorIsoCompQ _ 0).app N
  exact ⟨V.mapDerivedCategory.mapIso
      ((layerTensor X S N).mapIso a ≪≫ T.mapIso ((Iso.refl _).prod s) ≪≫ c C' hk N) ≪≫
    V.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso q ≪≫
    (derivedChangeComplexIso X (φ (n + 1))
      (finiteModelConstantComplex X _ (finiteQuotientLayerTensorComplex d.ideal n P))).symm⟩

/--
The actual finite quotient layer and its derived constant tensor model become
isomorphic after restriction to the etale chart.  This is the derived-object
comparison before applying exact slice homology.  It is the unresolved derived
tensor and balancing step of the finite-layer argument.

Source: Stacks Project, sites-cohomology.tex, Tags 094I and 06YU.
Proof: identify the kernel of the successive quotient with the ideal-power
layer, use the compatible coefficient maps to balance the derived tensor, and
transport the supplied residue-chart isomorphism through the derived tensor
descent equivalence.  Restriction to the chart is exact and retains the
successor coefficient action.
(blueprint: lem-weil-pbc-finite-quotient-layer-tensor-derived-slice-comparison).
-/
theorem finiteQuotient_layer_tensor_derived_slice_comparison
    (X : Scheme.{t})
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n))
    (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d))
    (b : ℤ) (n : ℕ) (Z : X.Etale)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (0 + 1))) ℤ)
    (hPb : P.IsStrictlyLE b)
    (hP : ∀ i : ℤ, Module.Projective (A ⧸ d.ideal ^ (0 + 1)) (P.X i))
    (e : Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d 0)
          ((toProEt X).obj Z) ((completedAdicQuotientReduction X d 0).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d 0)
          ((toProEt X).obj Z) ((completedAdicDerivedChange X (φ 0)).obj
            (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P))))) :
    Nonempty
      ((ringedDerivedRestrictionGeneral (completedAdicFiniteRing X d (n + 1))
          ((toProEt X).obj Z)).obj (finiteQuotientLayerObject X d M n) ≅
        (ringedDerivedRestrictionGeneral (completedAdicFiniteRing X d (n + 1))
          ((toProEt X).obj Z)).obj
          ((completedAdicDerivedChange X (φ (n + 1))).obj
            (DerivedCategory.Q.obj
              (finiteModelConstantComplex X _
                (finiteQuotientLayerTensorComplex d.ideal n P))))) := by
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  let R := completedAdicFiniteCommRing X d (n + 1)
  let S := completedAdicFiniteCommRing X d 0
  let f := completedAdicQuotientCommMap X d (n + 1) 0 (Nat.zero_le _)
  let U := (toProEt X).obj Z
  let N := (finiteCoefficientConstantFunctor X _ (φ 0)).obj
    (finiteQuotientLayerModule d.ideal n)
  let M₀ := (completedAdicQuotientReduction X d 0).obj M
  let M₁ := (completedAdicQuotientReduction X d (n + 1)).obj M
  let P₀ := (completedAdicDerivedChange X (φ 0)).obj
    (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P))
  let F := (layerRes X f).mapDerivedCategory
  let T := layerTensor X S N
  let rR := ringedDerivedRestrictionGeneral (completedAdicFiniteRing X d (n + 1)) U
  let rS := ringedDerivedRestrictionGeneral (completedAdicFiniteRing X d 0) U
  have := layerSliceRes_limits X U f
  have := layerSliceRes_colimits X U f
  let F' := (layerSliceRes X U f).mapDerivedCategory
  let T' := layerSliceTensor X S U N
  obtain ⟨kernelIso⟩ := finiteQuotient_layer_kernel_constant_comparison X d φ hφ hcompat n
  let e₀ : (completedAdicDerivedChange X f).obj M₁ ≅ M₀ :=
    (residueChange_comp X (completedAdicCommProjection X d (n + 1)) f).app M ≪≫
      (eqToIso (congrArg (fun g ↦ completedAdicDerivedChange X g)
        (completedAdicCommProjection_comp X d (n + 1) 0 (Nat.zero_le _)))).app M
  obtain ⟨balance⟩ := layerProjection X f M₁ N
  let a : finiteQuotientLayerObject X d M n ≅ F.obj (T.obj M₀) :=
    (SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X) R).mapIso
      ((Iso.refl M₁).prod ((DerivedCategory.singleFunctor _ 0).mapIso kernelIso)) ≪≫
        balance ≪≫ F.mapIso (T.mapIso e₀)
  obtain ⟨scalarOver⟩ := layerRes_over X U f
  let overIso (K : DerivedCategory (layerModules X S)) :
      rR.obj (F.obj (T.obj K)) ≅ F'.obj (T'.obj (rS.obj K)) :=
    scalarOver.app (T.obj K) ≪≫
      F'.mapIso (layerTensor_over X S U K N).some
  let chartIso : rS.obj M₀ ≅ rS.obj P₀ :=
    residueRestrictionComparison X (completedAdicFiniteRing X d 0) U M₀ ≪≫ e.some ≪≫
      (residueRestrictionComparison X (completedAdicFiniteRing X d 0) U P₀).symm
  obtain ⟨compute⟩ := layerChartComputation X d φ hφ hcompat n P b hPb hP
  exact ⟨rR.mapIso a ≪≫ overIso M₀ ≪≫
    F'.mapIso (T'.mapIso chartIso) ≪≫ (overIso P₀).symm ≪≫ rR.mapIso compute⟩

end AlgebraicGeometry.Scheme
