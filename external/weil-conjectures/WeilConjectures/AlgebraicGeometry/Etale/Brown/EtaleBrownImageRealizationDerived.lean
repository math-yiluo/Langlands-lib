/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! Derived part of the normalized image realization.

(blueprint: lem-pur-etale-brown-image-realization-derived)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

private theorem constant_equivalence
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u}) (n : ℕ) :
    (strictEtaleBrownConstant O t W n).IsEquivalence := by
  let J := W.smallEtaleTopology
  let R := strictEtaleBrownRing O t n
  let c := (constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of R)
  have hunit :
      Functor.whiskerRight (toSheafify J ((Functor.const W.Etaleᵒᵖ).obj (.of R)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫ c.hom.hom =
      toSheafify J ((Functor.const W.Etaleᵒᵖ).obj (RingCat.of R)) := by
    dsimp only [c, Iso.app_hom]
    rw [constantCommuteCompose_hom_app_hom]
    rw [← Category.assoc, sheafComposeIso_inv_fac]
    exact (toSheafify_naturality J
      (Functor.constComp W.Etaleᵒᵖ (CommRingCat.of R)
        (forget₂ CommRingCat RingCat)).hom).symm.trans (by rfl)
  have hsmul (M : strictEtaleLevel W O t n) (U : W.Etaleᵒᵖ)
      (a : R) (x : M.val.obj U) :
      a • (show ((ConstantScalarRestriction.restriction J R).obj M).obj.obj U from x) =
        a • (show ((strictEtaleBrownConstant O t W n).obj M).obj.obj U from x) := by
    have h := congrArg (fun f ↦ f.app U a) hunit
    have hi := congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    change c.inv.hom.app U
      ((toSheafify J ((Functor.const W.Etaleᵒᵖ).obj (RingCat.of R))).app U a) • x = _
    erw [← h]
    exact congrArg (fun b ↦ b • x) (ConcreteCategory.congr_hom hi _)
  let e : ConstantScalarRestriction.restriction J R ≅ strictEtaleBrownConstant O t W n := by
    refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
      (NatIso.ofComponents (fun U ↦ ?_) ?_)) ?_
    · exact ModuleCat.isoMk (Iso.refl _) (fun a ↦ by
        ext x
        exact (hsmul M U a x).symm)
    · intro U U' f
      ext x
      rfl
    · intro M M' f
      ext U x
      rfl
  have : (ConstantScalarRestriction.restriction J R).IsEquivalence :=
    ConstantScalarRestriction.isEquivalence J R
  exact Functor.isEquivalence_of_iso e

/-- Construction of the normalized derived direct-image comparison.
Source: Zheng, Lemma 5.16; Stacks 07A4.
(blueprint: lem-pur-etale-brown-image-realization-derived).

The universal right-derived unit determines the comparison and its representative
equation after transport through the supplied Brown realizations.
-/
theorem etaleBrownImageRealization_right_exists
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (ordinaryRight : A.right n ⋙ strictEtaleBrownConstant O t W n ≅
      strictEtaleBrownConstant O t V n ⋙
        Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)
    (hordinary : ∀ (M : strictEtaleLevel V O t n) (U : W.Etaleᵒᵖ)
      (x : ((A.right n).obj M).val.obj U),
      (ordinaryRight.hom.app M).hom.app U x =
        ((A.rightUnderlying n).hom.app M).hom.app U x) :
    ∃ right : B.direct ⋙ RW.derived n ≅ RV.derived n ⋙
      (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).rightDerivedFunctor,
      (letI := RV.val.ordinaryAdditive
       letI := RW.val.ordinaryAdditive
       ∀ K : CochainComplex (strictEtaleLevel V O t n) ℤ,
         (RW.derived n).map (B.directUnit.app K) ≫
             right.hom.app (DerivedCategory.Q.obj K) ≫
             (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
               g).rightDerivedFunctor.map ((RV.factors n).hom.app K) =
           (RW.factors n).hom.app (((A.right n).mapHomologicalComplex (.up ℤ)).obj K) ≫
             DerivedCategory.Q.map
               ((NatTrans.mapHomologicalComplex ordinaryRight.hom (.up ℤ)).app K) ≫
             strictEtaleBrownRightUnit O t g n
               (((strictEtaleBrownConstant O t V n).mapHomologicalComplex
                 (.up ℤ)).obj K)) := by
  classical
  have _hordinary := hordinary
  have := RV.val.ordinaryAdditive
  have := RW.val.ordinaryAdditive
  have : (strictEtaleBrownConstant O t V n).IsEquivalence :=
    constant_equivalence O t V n
  have : (strictEtaleBrownConstant O t V n).PreservesKInjectiveComplexes := inferInstance
  have : IsGrothendieckAbelian.{u + 1} (strictEtaleLevel V O t n) :=
    isGrothendieckAbelian_coefficientUniverse _
  have : Abelian.HasKInjectiveResolutions (strictEtaleLevel V O t n) := inferInstance
  let F := A.right n
  let G := Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g
  let x := strictEtaleBrownConstant O t V n
  let y := strictEtaleBrownConstant O t W n
  let etaG : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G.rightDerivedFunctor :=
    { app := strictEtaleBrownRightUnit O t g n
      naturality := by
        intro K L f
        change DerivedCategory.Q.map ((G.mapHomologicalComplex _).map f) ≫
            G.rightDerivedFunctorUnitQ L =
          G.rightDerivedFunctorUnitQ K ≫ G.rightDerivedFunctor.map (DerivedCategory.Q.map f)
        exact G.rightDerivedFunctorUnitQ_naturality f }
  let cc := NatIso.mapHomologicalComplex ordinaryRight (.up ℤ)
  let etaL : (F ⋙ y).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (B.direct ⋙ RW.derived n) :=
    whiskerLeft (F.mapHomologicalComplex (.up ℤ)) (RW.factors n).inv ≫
      whiskerRight B.directUnit (RW.derived n)
  let etaR : (F ⋙ y).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (RV.derived n ⋙ G.rightDerivedFunctor) :=
    whiskerRight cc.hom DerivedCategory.Q ≫
      whiskerLeft (x.mapHomologicalComplex (.up ℤ)) etaG ≫
      whiskerRight (RV.factors n).inv G.rightDerivedFunctor
  have hL : (B.direct ⋙ RW.derived n).IsRightDerivedFunctor etaL
      (HomologicalComplex.quasiIso (strictEtaleLevel V O t n) (.up ℤ)) := by
    apply (derives (F ⋙ y)).isRightDerivedFunctor_of_isIso etaL
    intro I
    have := B.computes I.obj I.property
    change IsIso ((RW.factors n).inv.app _ ≫ (RW.derived n).map (B.directUnit.app I.obj))
    infer_instance
  have hR : (RV.derived n ⋙ G.rightDerivedFunctor).IsRightDerivedFunctor etaR
      (HomologicalComplex.quasiIso (strictEtaleLevel V O t n) (.up ℤ)) := by
    apply (derives (F ⋙ y)).isRightDerivedFunctor_of_isIso etaR
    intro I
    have := I.property
    have : CochainComplex.IsKInjective
        ((x.mapHomologicalComplex (.up ℤ)).obj I.obj) := inferInstance
    have hG : IsIso (etaG.app ((x.mapHomologicalComplex (.up ℤ)).obj I.obj)) := by
      change IsIso (G.rightDerivedFunctorUnitQ _)
      rw [G.rightDerivedFunctorUnitQ_eq]
      infer_instance
    change IsIso (DerivedCategory.Q.map (cc.hom.app I.obj) ≫
      etaG.app ((x.mapHomologicalComplex (.up ℤ)).obj I.obj) ≫
      G.rightDerivedFunctor.map ((RV.factors n).inv.app I.obj))
    infer_instance
  let e := Functor.rightDerivedUnique (B.direct ⋙ RW.derived n)
    (RV.derived n ⋙ G.rightDerivedFunctor) etaL etaR
    (HomologicalComplex.quasiIso (strictEtaleLevel V O t n) (.up ℤ))
  refine ⟨e, ?_⟩
  intro K
  have h : etaL.app K ≫ e.hom.app (DerivedCategory.Q.obj K) = etaR.app K := by
    simpa only [e, Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
      Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
      Functor.rightDerivedNatTrans_app _ _ etaL etaR
        (HomologicalComplex.quasiIso (strictEtaleLevel V O t n) (.up ℤ)) (𝟙 _) K
  have hh := congrArg (fun z ↦ (RW.factors n).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫ z ≫
        G.rightDerivedFunctor.map ((RV.factors n).hom.app K)) h
  simp only [etaL, etaR, cc, NatIso.mapHomologicalComplex, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Category.assoc, Iso.hom_inv_id_app_assoc,
    ← G.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app, etaG] at hh
  erw [G.rightDerivedFunctor.map_id, Category.comp_id] at hh
  exact hh

end AlgebraicGeometry
