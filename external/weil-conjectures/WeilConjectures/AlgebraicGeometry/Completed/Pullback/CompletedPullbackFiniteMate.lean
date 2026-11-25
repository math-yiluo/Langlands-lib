/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionData
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
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
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import all WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionData

/-! # The finite scalar mate of the pulled quotient augmentation

Source: Stacks Tag 099N (5).
(blueprint: lem-weil-pbc-completed-pullback-finite-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

attribute [local instance] completedReductionModuleTowerFunctor_additive
attribute [local instance] completedTowerModulePullback_additive

private theorem projectionOfAugmentation
    {B T : Type*} [Category B] [Category T]
    (D : B ⥤ T) (R : T ⥤ B) (E : T ⥤ B) (adj : D ⊣ R)
    (e : D ⋙ E ≅ 𝟭 B) (M : B) (H : T) (a : D.obj M ⟶ H) :
    (adj.unit.app M ≫ R.map a) ≫
        (e.inv.app (R.obj H) ≫ E.map (adj.counit.app H)) =
      e.inv.app M ≫ E.map a := by
  have hn := e.inv.naturality (adj.unit.app M ≫ R.map a)
  change (adj.unit.app M ≫ R.map a) ≫ e.inv.app (R.obj H) =
    e.inv.app M ≫ E.map (D.map (adj.unit.app M ≫ R.map a)) at hn
  rw [← Category.assoc, hn, Category.assoc, ← E.map_comp]
  congr 1
  congr 1
  rw [D.map_comp, Category.assoc, ← Functor.comp_map, adj.counit.naturality,
    ← Category.assoc]
  simp

private theorem comparison_projection
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) (n : ℕ) :
    completedPullbackComparison g d K ≫
        (completedReductionLimitProjection d (X := X) n).app
          ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj K)) =
      (constantEvaluationIso (pbcModules X (pbcAdicCompletion X d)) (op n)).inv.app
          ((completedOrdinaryPullback g d).obj K) ≫
        (pbcTowerEvaluation X (pbcAdicCompletion X d) n).map
          ((completedPullbackConstantIso g d).hom.app K ≫
            (completedTowerPullback g d).map ((completedReductionTowerUnit d Y).app K)) := by
  change completedPullbackComparison g d K ≫
    (completedRlimProjection X (d.completedRing X) n).app _ = _
  rw [← limitCounitProjection_eq d X n]
  unfold completedPullbackComparison limitCounitProjection
  rw [constantRlimUnit_eq]
  exact projectionOfAugmentation _ _ _ (d.constantRlimAdjunction X) _ _ _ _

private theorem evaluatedAugmentation
    {B T : Type*} [Category B] [Category T]
    (D : B ⥤ T) (E : T ⥤ B) (e : D ⋙ E ≅ 𝟭 B)
    {M N Z : B} {H H' H₀ : T}
    (c : M ⟶ N) (a : D.obj M ⟶ H) (b : H ⟶ H')
    (d : D.obj N ⟶ H₀) (v : H₀ ⟶ H')
    (q : E.obj H' ⟶ Z) (p : E.obj H₀ ⟶ N) (w : N ⟶ Z)
    (hab : a ≫ b = D.map c ≫ d ≫ v)
    (hd : E.map d ≫ p = e.hom.app N)
    (hv : E.map v ≫ q = p ≫ w) :
    e.inv.app M ≫ E.map a ≫ E.map b ≫ q = c ≫ w := by
  rw [← E.map_comp_assoc, hab, E.map_comp, E.map_comp]
  simp only [Category.assoc]
  rw [hv, ← Category.assoc (E.map d), hd]
  have hn := e.inv.naturality c
  change c ≫ e.inv.app N = e.inv.app M ≫ E.map (D.map c) at hn
  rw [← Category.assoc (e.inv.app M), ← hn]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private theorem counitOnComplex_eq
    {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (F : B ⥤ C) [F.Additive] (L : DerivedCategory B ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : CochainComplex B ℤ) :
    reductionComplexCounit F L ε K =
      ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj K) := by
  have hid : (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K = 𝟙 _ := rfl
  have hi : (DerivedCategory.quotientCompQhIso B).inv.app K = 𝟙 _ := rfl
  have hh : (DerivedCategory.quotientCompQhIso C).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
  simp only [reductionComplexCounit, hi, hh, hid]
  erw [L.map_id, (DerivedCategory.Qh (C := C)).map_id]
  simp only [Category.id_comp]
  erw [Category.comp_id, Category.comp_id]

private theorem comp_counitOnComplex_eq
    {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (F : B ⥤ C) [F.Additive] (L : DerivedCategory B ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : CochainComplex B ℤ) {M : DerivedCategory C}
    (a : M ⟶ L.obj (DerivedCategory.Q.obj K))
    (b : M ⟶ DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K))
    (h : a ≫ ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj K) = b) :
    a ≫ reductionComplexCounit F L ε K = b := by
  rw [counitOnComplex_eq]
  exact h

attribute [local irreducible] HasDerivedCategory.standard completedReductionTower
  completedReductionModuleTowerFunctor Functor.mapHomotopyCategory
  Functor.mapHomotopyCategoryFactors in
private theorem towerAugmentation_computed
    (T : Scheme.{u}) (P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      T.ProEt inferInstance (essentiallySmallSelf.{0} _) (ProEt.topology T)
      (pbcAdicCompletion T d) P) :
    letI := completedReductionModuleTowerFunctor_additive T d
    (completedReductionTowerUnit d T).app (DerivedCategory.Q.obj P) ≫
        completedReductionTowerComplexCounit T d P =
      (completedTowerConstant d T).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (completedReductionModuleUnit d T) (.up ℤ)).app P) := by
  let := completedReductionModuleTowerFunctor_additive T d
  have h := (completedReductionTowerUnit_exists d T).exists.choose_spec P hP
  have hi₁ : (DerivedCategory.quotientCompQhIso
      (pbcModules T (pbcAdicCompletion T d))).inv.app P = 𝟙 _ := rfl
  have hi₂ : (DerivedCategory.quotientCompQhIso
      (reductionModules T (completedReductionCoefficient T d))).inv.app P = 𝟙 _ := rfl
  dsimp only [HasCompletedReductionTowerUnitNormalization, completedReductionTowerUnit,
    completedReductionTowerComplexCounit, reductionComplexCounit,
    completedReductionTowerCounit, coherenceReductionTowerCounit,
    completedReductionComplexTowerFunctor] at h ⊢
  erw [hi₁, CategoryTheory.Functor.map_id, Category.id_comp] at h
  erw [hi₂, CategoryTheory.Functor.map_id, Category.id_comp]
  exact h

private theorem pulledAugmentation_computed
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{0} _) (ProEt.topology Y)
      (pbcAdicCompletion Y d) P) :
    letI := completedReductionModuleTowerFunctor_additive Y d
    ((completedPullbackConstantIso g d).hom.app (DerivedCategory.Q.obj P) ≫
        (completedTowerPullback g d).map
          ((completedReductionTowerUnit d Y).app (DerivedCategory.Q.obj P))) ≫
      ((completedTowerPullback g d).map (completedReductionTowerComplexCounit Y d P) ≫
        completedTowerPullbackComplexCounit g d
          ((completedReductionComplexTowerFunctor Y d).obj P)) =
    (completedDerivedConstant d X).map (completedOrdinaryPullbackComplexCounit g d P) ≫
      (completedTowerConstant d X).mapDerivedCategoryFactors.hom.app
        (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (eqToHom (completedPullbackConstantComplex_eq g d P)) ≫
      DerivedCategory.Q.map (((completedTowerModulePullback g d).mapHomologicalComplex
        (.up ℤ)).map ((NatTrans.mapHomologicalComplex
          (completedReductionModuleUnit d Y) (.up ℤ)).app P)) := by
  with_unfolding_all
    let := completedReductionModuleTowerFunctor_additive Y d
    let u := (NatTrans.mapHomologicalComplex (completedReductionModuleUnit d Y) (.up ℤ)).app P
    have hu := towerAugmentation_computed d Y P hP
    have hn := (completedReductionPullbackComplexNat g d).naturality u
    have hc := (completedPullbackConstantIso_exists g d).exists.choose_spec P hP
    change _ = _ at hc
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hu, Functor.map_comp]
    have hn' : (completedTowerPullback g d).map (DerivedCategory.Q.map u) ≫
        completedTowerPullbackComplexCounit g d
          ((completedReductionComplexTowerFunctor Y d).obj P) =
      completedTowerPullbackComplexCounit g d
          (((completedTowerConstant d Y).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).map u) := hn
    simp only [Category.assoc]
    rw [hn']
    simpa only [u, Category.assoc, completedPullbackConstantIso] using congrArg
      (fun t ↦ t ≫ DerivedCategory.Q.map
        (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).map u)) hc.symm

private def ordinaryFiniteAugmentation (n : ℕ) :
    completedModulePullback g d ⟶
      reductionChange Y (completedReductionProjection Y d n) ⋙
        completedReductionFiniteModules g d n ⋙
          pbcRestrict (completedReductionProjection X d n) where
  app M := (completedModulePullback g d).map
      (((completedReductionModuleUnit d Y).app M).app (op n)) ≫
    (completedReductionOrdinaryComparison g d n).hom.app M
  naturality M N f := by
    have hu := (completedReductionModuleUnit d Y).naturality f
    have h := congrArg (fun t ↦ t.app (op n)) hu
    change f ≫ ((completedReductionModuleUnit d Y).app N).app (op n) =
      ((completedReductionModuleUnit d Y).app M).app (op n) ≫
        (completedReductionLevel Y d n).map f at h
    rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc]
    exact congrArg (_ ≫ ·) ((completedReductionOrdinaryComparison g d n).hom.naturality f)

private def finiteExactPullbackIso : completedModulePullback g d ≅
    proEtaleRingModulePullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (@asIso _ _ _ _ (completedCoefficientMap g d) (coefficientMap_isIso g d)) :=
  NatIso.ofComponents (fun M ↦ eqToIso
    (reductionChange_obj_eq X (completedCoefficientMap g d)
      ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).obj M))) (by
    intro M N f
    dsimp only [completedModulePullback, Functor.comp_map, proEtaleRingModulePullback,
      proEtaleRingModulePullbackMap]
    rw [reductionChange_map_eq]
    simp)

private theorem naturality_comp_fast
    {B C : Type*} [Category B] [Category C] {F G : B ⥤ C}
    (e : F ⟶ G) {M N : B} (u : M ⟶ N) {Z : C} (t : G.obj N ⟶ Z) :
    F.map u ≫ (e.app N ≫ t) = e.app M ≫ (G.map u ≫ t) := by
  rw [← Category.assoc, e.naturality, Category.assoc]

private theorem transpose_isIso_fast
    {B C : Type*} [Category B] [Category C] {L : B ⥤ C} {R : C ⥤ B}
    (adj : L ⊣ R) {M N : B} {Z : C}
    (e : M ⟶ N) [IsIso e] (m : L.obj N ⟶ Z) [IsIso m] :
    IsIso ((adj.homEquiv M Z).symm (e ≫ adj.homEquiv N Z m)) := by
  rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  infer_instance

-- Compare the actual tensor mate through the two chosen coefficient isomorphisms.
private theorem ordinaryFiniteMate_isIso (n : ℕ)
    (M : pbcModules Y (pbcAdicCompletion Y d)) :
    IsIso (((pbcScalarAdjunction (completedReductionProjection X d n)).homEquiv _ _).symm
      ((ordinaryFiniteAugmentation g d n).app M)) := by
  with_unfolding_all
    have he : completedReductionOrdinaryComparison g d n = ordinaryIsoCandidate g d n :=
      (completedReductionOrdinaryComparison_exists g d n).unique
        (completedReductionOrdinaryComparison_exists g d n).exists.choose_spec
        (ordinaryIsoCandidate_normalized g d n)
    let cB := @asIso _ _ _ _ (completedCoefficientMap g d) (coefficientMap_isIso g d)
    let cS := asIso (completedFiniteCoefficientMap g d n)
    let b := proEtaleRingRestrictionPullbackInv g
      (pbcAdicCompletion Y d) (reductionCoefficient Y d n)
      (pbcAdicCompletion X d) (reductionCoefficient X d n)
      (completedReductionProjection Y d n) (completedReductionProjection X d n)
      cB cS (limit.lift_π _ (op n))
    let mu := ((mateEquiv (pbcScalarAdjunction (completedReductionProjection Y d n))
      (pbcScalarAdjunction (completedReductionProjection X d n))).symm
        (TwoSquare.mk _ _ _ _ b))
    have hB : cB = d.integralRingIso g := by
      apply Iso.ext
      exact completedCoefficientMap_eq_integralRingIso g d
    have hS : cS = d.finiteRingIso g n := by
      apply Iso.ext
      rfl
    have hm : IsIso (mu.app M) := by
      have H
          (b₀ : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (pbcAdicCompletion Y d) ≅ pbcAdicCompletion X d)
          (s₀ : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (reductionCoefficient Y d n) ≅ reductionCoefficient X d n)
          (hb : b₀ = d.integralRingIso g) (hs : s₀ = d.finiteRingIso g n)
          (hc : b₀.hom ≫ completedReductionProjection X d n =
            (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
              (completedReductionProjection Y d n) ≫ s₀.hom) :
          IsIso (((mateEquiv (pbcScalarAdjunction (completedReductionProjection Y d n))
            (pbcScalarAdjunction (completedReductionProjection X d n))).symm
              (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionPullbackInv g
                (pbcAdicCompletion Y d) (reductionCoefficient Y d n)
                (pbcAdicCompletion X d) (reductionCoefficient X d n)
                (completedReductionProjection Y d n) (completedReductionProjection X d n)
                b₀ s₀ hc))).app M) := by
        subst b₀
        subst s₀
        change IsIso ((completedOrdinaryReductionPullbackInv d g n).app M)
        infer_instance
      exact H cB cS hB hS (limit.lift_π _ (op n))
    have hu : ((completedReductionModuleUnit d Y).app M).app (op n) =
        (pbcScalarAdjunction (completedReductionProjection Y d n)).unit.app M := by
      ext U x
      exact ((completedReductionModuleUnit_exists d Y).exists.choose_spec M n U x).trans
        ((pbcScalarAdjunction_exists (completedReductionProjection Y d n)).exists.choose_spec
          M U x).symm
    have ht := unit_mateEquiv_symm
      (pbcScalarAdjunction (completedReductionProjection Y d n))
      (pbcScalarAdjunction (completedReductionProjection X d n)) (TwoSquare.mk _ _ _ _ b) M
    have ha : (ordinaryFiniteAugmentation g d n).app M =
        (finiteExactPullbackIso g d).hom.app M ≫
          (pbcScalarAdjunction (completedReductionProjection X d n)).homEquiv _ _
            (mu.app M) := by
      dsimp only [ordinaryFiniteAugmentation]
      rw [he, hu]
      unfold ordinaryIsoCandidate
      change (completedModulePullback g d).map _ ≫
        ((finiteExactPullbackIso g d).hom.app _ ≫ b.app _) = _
      exact (naturality_comp_fast (finiteExactPullbackIso g d).hom _ _).trans
        (congrArg ((finiteExactPullbackIso g d).hom.app M ≫ ·) ht)
    rw [ha]
    exact transpose_isIso_fast _ _ _

private def finiteAugmentation (n : ℕ) :
    completedOrdinaryPullback g d ⟶ completedReductionFiniteTarget g d n ⋙
      pbcDerivedRestrict (completedReductionProjection X d n) where
  app K := (constantEvaluationIso (pbcModules X (pbcAdicCompletion X d)) (op n)).inv.app
      ((completedOrdinaryPullback g d).obj K) ≫
    (pbcTowerEvaluation X (pbcAdicCompletion X d) n).map
      ((completedPullbackConstantIso g d).hom.app K ≫
        (completedTowerPullback g d).map ((completedReductionTowerUnit d Y).app K)) ≫
    (completedReductionFiniteEvaluation g d n).hom.app K
  naturality K K' v := by
    let a : completedOrdinaryPullback g d ⋙ completedDerivedConstant d X ⟶
        completedReductionTower Y d ⋙ completedTowerPullback g d :=
      (completedPullbackConstantIso g d).hom ≫
        Functor.whiskerRight (completedReductionTowerUnit d Y) (completedTowerPullback g d)
    have ha := a.naturality v
    have he := (constantEvaluationIso (pbcModules X (pbcAdicCompletion X d))
      (op n)).inv.naturality ((completedOrdinaryPullback g d).map v)
    simp only [Functor.comp_map, Functor.id_map] at he
    rw [← Category.assoc, he]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc]
    erw [ha]
    rw [Functor.map_comp, Category.assoc]
    have hf := (completedReductionFiniteEvaluation g d n).hom.naturality v
    simpa only [a, NatTrans.comp_app, Functor.whiskerRight_app, Functor.comp_map,
      Category.assoc] using congrArg
        (fun t ↦ (constantEvaluationIso (pbcModules X (pbcAdicCompletion X d))
          (op n)).inv.app ((completedOrdinaryPullback g d).obj K) ≫
            (pbcTowerEvaluation X (pbcAdicCompletion X d) n).map (a.app K) ≫ t) hf

private def ordinaryFiniteMate (n : ℕ) :
    completedModulePullback g d ⋙ pbcExtend (completedReductionProjection X d n) ⟶
      reductionChange Y (completedReductionProjection Y d n) ⋙
        completedReductionFiniteModules g d n :=
  (((pbcScalarAdjunction (completedReductionProjection X d n)).whiskerRight
    (pbcModules Y (pbcAdicCompletion Y d))).homEquiv _ _).symm
      (ordinaryFiniteAugmentation g d n)

private instance ordinaryFiniteMate_iso (n : ℕ) : IsIso (ordinaryFiniteMate g d n) := by
  let : ∀ M, IsIso ((ordinaryFiniteMate g d n).app M) := by
    intro M
    dsimp only [ordinaryFiniteMate]
    rw [transpose_symm_app]
    exact ordinaryFiniteMate_isIso g d n M
  exact NatIso.isIso_of_isIso_app _

private theorem evaluated_complex_augmentation
    {B C J : Type*} [Category B] [Preadditive B] [Category C] [Preadditive C]
    [Category J]
    [(Functor.const J : B ⥤ (J ⥤ B)).PreservesZeroMorphisms]
    [(Functor.const J : C ⥤ (J ⥤ C)).PreservesZeroMorphisms]
    (j : J) (F : B ⥤ C) [F.Additive]
    (U : B ⥤ (J ⥤ B)) [U.Additive] (V : B ⥤ C) [V.Additive]
    (η : (Functor.const J : B ⥤ (J ⥤ B)) ⟶ U)
    (e : U ⋙ (Functor.whiskeringRight J B C).obj F ⋙
      (CategoryTheory.evaluation J C).obj j ⟶ V)
    (α : F ⟶ V)
    (hα : ∀ M, α.app M = F.map ((η.app M).app j) ≫ e.app M)
    (P : CochainComplex B ℤ)
    (h : ((Functor.const J : C ⥤ (J ⥤ C)).mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj P) =
        (((Functor.whiskeringRight J B C).obj F).mapHomologicalComplex (.up ℤ)).obj
          (((Functor.const J : B ⥤ (J ⥤ B)).mapHomologicalComplex (.up ℤ)).obj P)) :
    (((CategoryTheory.evaluation J C).obj j).mapHomologicalComplex (.up ℤ)).map
        (eqToHom h ≫
          (((Functor.whiskeringRight J B C).obj F).mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex η (.up ℤ)).app P)) ≫
      (NatTrans.mapHomologicalComplex e (.up ℤ)).app P =
        (NatTrans.mapHomologicalComplex α (.up ℤ)).app P := by
  apply HomologicalComplex.hom_ext
  intro i
  simp only [Functor.map_comp, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f, Category.assoc]
  change (((eqToHom h).f i).app j) ≫
      F.map ((η.app (P.X i)).app j) ≫ e.app (P.X i) = α.app (P.X i)
  simp only [HomologicalComplex.eqToHom_f, eqToHom_app, eqToHom_refl,
    Category.id_comp, hα]

private theorem evaluatedAugmentation_normalized
    {B T : Type*} [Category B] [Category T]
    (D : B ⥤ T) (E : T ⥤ B) (e : D ⋙ E ≅ 𝟭 B)
    {M N Z Z₀ Z₁ : B} {H H' H₀ : T}
    (c : M ⟶ N) (a : D.obj M ⟶ H) (b : H ⟶ H')
    (d : D.obj N ⟶ H₀) (v : H₀ ⟶ H')
    (q : E.obj H' ⟶ Z) (p : E.obj H₀ ⟶ N) (w : N ⟶ Z)
    (k : E.obj H ⟶ Z₀) (r : Z₀ ⟶ Z₁) (s : Z₁ ⟶ Z)
    (hnorm : E.map b ≫ q = k ≫ r ≫ s)
    (hab : a ≫ b = D.map c ≫ d ≫ v)
    (hd : E.map d ≫ p = e.hom.app N)
    (hv : E.map v ≫ q = p ≫ w) :
    (e.inv.app M ≫ E.map a ≫ k) ≫ r ≫ s = c ≫ w := by
  simp only [Category.assoc]
  rw [← hnorm]
  exact evaluatedAugmentation D E e c a b d v q p w hab hd hv

private theorem derived_naturality_comp_fast
    {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (F : B ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {M N : CochainComplex B ℤ}
    (u : M ⟶ N) {Z : CochainComplex C ℤ}
    (t : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ Z) :
    F.mapDerivedCategory.map (DerivedCategory.Q.map u) ≫
        (F.mapDerivedCategoryFactors.hom.app N ≫ DerivedCategory.Q.map t) =
      F.mapDerivedCategoryFactors.hom.app M ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map u ≫ t) := by
  rw [← Category.assoc]
  erw [F.mapDerivedCategoryFactors.hom.naturality u]
  simp only [Functor.comp_map, Category.assoc, Functor.map_comp]

private theorem derived_naturality_comp_of_eq
    {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (F : B ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {M N : CochainComplex B ℤ} (u : M ⟶ N) {Z : CochainComplex C ℤ}
    (t : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ Z)
    (v : (F.mapHomologicalComplex (.up ℤ)).obj M ⟶ Z)
    (h : (F.mapHomologicalComplex (.up ℤ)).map u ≫ t = v) :
    F.mapDerivedCategory.map (DerivedCategory.Q.map u) ≫
        (F.mapDerivedCategoryFactors.hom.app N ≫ DerivedCategory.Q.map t) =
      F.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map v := by
  rw [derived_naturality_comp_fast, h]

attribute [local irreducible] HasDerivedCategory.standard completedModulePullback
  completedReductionModuleTowerFunctor reductionChange completedReductionTower
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors in
private theorem finiteAugmentation_computed (n : ℕ)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{0} _) (ProEt.topology Y)
      (pbcAdicCompletion Y d) P) :
    (finiteAugmentation g d n).app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedRestrict (completedReductionProjection X d n)).map
          (completedReductionFiniteModelMap g d n P) ≫
        (pbcRestrict (completedReductionProjection X d n)).mapDerivedCategoryFactors.hom.app
          (((completedReductionFiniteModules g d n).mapHomologicalComplex (.up ℤ)).obj
            (((reductionChange Y (completedReductionProjection Y d n)).mapHomologicalComplex
              (.up ℤ)).obj P)) =
      completedOrdinaryPullbackComplexCounit g d P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (ordinaryFiniteAugmentation g d n) (.up ℤ)).app P) := by
  let := completedReductionModuleTowerFunctor_additive Y d
  let E := (CategoryTheory.evaluation ℕᵒᵖ
    (pbcModules X (pbcAdicCompletion X d))).obj (op n)
  let P' := ((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P
  let JT := ((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
    ((completedReductionComplexTowerFunctor Y d).obj P)
  let a := (completedPullbackConstantIso g d).hom.app (DerivedCategory.Q.obj P) ≫
    (completedTowerPullback g d).map ((completedReductionTowerUnit d Y).app
      (DerivedCategory.Q.obj P))
  let b := (completedTowerPullback g d).map (completedReductionTowerComplexCounit Y d P) ≫
    completedTowerPullbackComplexCounit g d ((completedReductionComplexTowerFunctor Y d).obj P)
  let u := eqToHom (completedPullbackConstantComplex_eq g d P) ≫
    ((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (completedReductionModuleUnit d Y) (.up ℤ)).app P)
  let t := (NatTrans.mapHomologicalComplex
    (completedReductionOrdinaryComparison g d n).hom (.up ℤ)).app P
  have hn := (completedReductionFiniteEvaluation_exists g d n).exists.choose_spec
  change HasCompletedReductionFiniteEvaluationNormalization g d n
    (completedReductionFiniteEvaluation g d n) at hn
  unfold HasCompletedReductionFiniteEvaluationNormalization
    completedReductionComparisonNormalized at hn
  have hn' := hn P hP
  dsimp only [completedReductionPulledModelNat, completedReductionFiniteModelNat,
    completedReductionCompositeCounitNat, completedReductionTowerComplexNat,
    completedReductionPullbackComplexNat, completedReductionComplexCounitNat,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hn'
  have hε : (pbcExtend (completedReductionProjection Y d n)).leftDerivedCounitOnComplex
      (pbcDerivedExtend (completedReductionProjection Y d n))
      (pbcExtensionCounit (completedReductionProjection Y d n)) P =
      pbcComplexCounit (completedReductionProjection Y d n) P := by rfl
  rw [hε] at hn'
  simp only [Category.assoc] at hn'
  change E.mapDerivedCategory.map b ≫ E.mapDerivedCategoryFactors.hom.app JT ≫
      DerivedCategory.Q.map t =
    (completedReductionFiniteEvaluation g d n).hom.app (DerivedCategory.Q.obj P) ≫
      (pbcDerivedRestrict (completedReductionProjection X d n)).map
        (completedReductionFiniteModelMap g d n P) ≫ _ at hn'
  dsimp only [completedReductionRestrictionFactors] at hn'
  have hv : E.mapDerivedCategory.map (DerivedCategory.Q.map u) ≫
      (E.mapDerivedCategoryFactors.hom.app JT ≫ DerivedCategory.Q.map t) =
    E.mapDerivedCategoryFactors.hom.app
        (((completedTowerConstant d X).mapHomologicalComplex (.up ℤ)).obj P') ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (ordinaryFiniteAugmentation g d n) (.up ℤ)).app P) := by
    apply derived_naturality_comp_of_eq E u t
    exact evaluated_complex_augmentation (op n) (completedModulePullback g d)
      (completedReductionModuleTowerFunctor Y d) _ (completedReductionModuleUnit d Y)
      (completedReductionOrdinaryComparison g d n).hom (ordinaryFiniteAugmentation g d n)
      (fun _ ↦ rfl) P (completedPullbackConstantComplex_eq g d P)
  exact evaluatedAugmentation_normalized (completedDerivedConstant d X) E.mapDerivedCategory
    (constantEvaluationIso (pbcModules X (pbcAdicCompletion X d)) (op n))
    (completedOrdinaryPullbackComplexCounit g d P) a b
    ((completedTowerConstant d X).mapDerivedCategoryFactors.hom.app P')
    (DerivedCategory.Q.map u)
    (E.mapDerivedCategoryFactors.hom.app JT ≫ DerivedCategory.Q.map t)
    (E.mapDerivedCategoryFactors.hom.app
      (((completedTowerConstant d X).mapHomologicalComplex (.up ℤ)).obj P'))
    (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (ordinaryFiniteAugmentation g d n) (.up ℤ)).app P))
    _ _ _ hn'
    (by simpa only [a, b, u, P', Functor.map_comp, Category.assoc] using
      pulledAugmentation_computed g d P hP)
    (constantEvaluation_factors _ (op n) P').symm hv

private def finiteMate (n : ℕ) :
    completedOrdinaryPullback g d ⋙
      reductionDerivedChange X (completedReductionProjection X d n) ⟶
        completedReductionFiniteTarget g d n :=
  (((pbcDerivedScalarAdjunction (completedReductionProjection X d n)).whiskerRight
    (DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))).homEquiv _ _).symm
      (finiteAugmentation g d n)

private theorem finiteMate_app
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) (n : ℕ) :
    (finiteMate g d n).app K =
      (reductionDerivedChange X (completedReductionProjection X d n)).map
          (completedPullbackComparison g d K) ≫ completedPullbackReductionArrow g d K n := by
  with_unfolding_all
    dsimp only [finiteMate]
    rw [transpose_symm_app]
    dsimp only [completedPullbackReductionArrow]
    rw [← Adjunction.homEquiv_naturality_left_symm]
    congr 1
    dsimp only [finiteAugmentation]
    simpa only [Category.assoc] using congrArg
      (fun t ↦ t ≫ (completedReductionFiniteEvaluation g d n).hom.app K)
        (comparison_projection g d K n).symm

private theorem finitePullback_good {U V : Scheme.{u}} (f : U ⟶ V)
    (R : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (P : CochainComplex (proEtaleRingModules V R) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      V.ProEt inferInstance (essentiallySmallSelf.{0} V.ProEt) (ProEt.topology V) R P)
    (hflat : ∀ n : ℤ, @SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      V.ProEt inferInstance (ProEt.topology V) inferInstance
      (WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} V)
      (WeilConjectures.integralCoefficientAbSheafify.{u, u} V).isRightAdjoint R (P.X n)) :
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      U.ProEt inferInstance (essentiallySmallSelf.{0} U.ProEt) (ProEt.topology U) S
      (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P) ∧
    ∀ n : ℤ, @SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      U.ProEt inferInstance (ProEt.topology U) inferInstance
      (WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} U)
      (WeilConjectures.integralCoefficientAbSheafify.{u, u} U).isRightAdjoint S
      ((((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P).X n) := by
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists.{u} f R
  have : PreservesFiniteLimits (proEtaleSheafInverseImage f (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 V)).2.2.2.1
  let IM : proEtaleRingModules V R ⥤ proEtaleRingModules U
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) :=
    @SheafOfModules.AlgebraicInverseImage.modules.{u + 1, u + 1, u, u + 1, u}
      V.ProEt U.ProEt inferInstance inferInstance (essentiallySmallSelf.{0} V.ProEt)
      (essentiallySmallSelf.{0} U.ProEt) (ProEt.topology V) (ProEt.topology U)
      (proEtaleSheafInverseImage f (Type (u + 1))) R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) I
  let C := proEtaleRingModules V R
  let D := proEtaleRingModules U ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
  have hobj (N : C) : (proEtaleRingModulePullback f R S c).obj N =
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} c.hom
        (IM.obj N) :=
    congrArg (SheafOfModules.changeOfRings.{u, u + 1, u + 1} c.hom)
      (Functor.congr_obj hI.symm N)
  refine @SheafOfModules.isKFlat_ringedToposPullback.{u + 1, u, u + 1, u, u + 1}
    V.ProEt U.ProEt inferInstance inferInstance (essentiallySmallSelf.{0} V.ProEt)
    (essentiallySmallSelf.{0} U.ProEt) (ProEt.topology V) (ProEt.topology U) R S
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1))) inferInstance I c.hom
    (proEtaleRingModulePullback f R S c) hobj ?_ inferInstance P hP hflat
  intro M N a
  have aux (F G : C ⥤ D) (h : F = G) :
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} c.hom (F.obj M) (F.map a) =
        eqToHom (congrArg (fun E : C ⥤ D ↦
          SheafOfModules.changeOfRings.{u, u + 1, u + 1} c.hom (E.obj M)) h) ≫
        SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} c.hom (G.obj M) (G.map a) ≫
        eqToHom (congrArg (fun E : C ⥤ D ↦
          SheafOfModules.changeOfRings.{u, u + 1, u + 1} c.hom (E.obj N)) h).symm := by
    subst G
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact aux (proEtaleModuleInverseImage f R) IM hI.symm

private theorem finiteCounit_eq
    {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (F : B ⥤ C) [F.Additive] (L : DerivedCategory B ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : CochainComplex B ℤ) :
    reductionComplexCounit F L ε K =
      ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj K) := by
  have hid : (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K = 𝟙 _ := rfl
  have hi : (DerivedCategory.quotientCompQhIso B).inv.app K = 𝟙 _ := rfl
  have hh : (DerivedCategory.quotientCompQhIso C).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
  simp only [reductionComplexCounit, hi, hh, hid]
  erw [L.map_id, (DerivedCategory.Qh (C := C)).map_id]
  simp only [Category.id_comp]
  erw [Category.comp_id, Category.comp_id]

private theorem finiteCanonicalTranspose (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    ∀ (P : CochainComplex (reductionModules T R) ℤ)
      (K : CochainComplex (reductionModules T S) ℤ)
      (f : ((reductionChange T a).mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
    (pbcDerivedScalarAdjunction a).homEquiv _ _
      (pbcComplexCounit a P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
          (((pbcScalarAdjunction a).mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
            (reductionRestrict T a).mapDerivedCategoryFactors.inv.app K := by
  obtain ⟨ad, had⟩ := SheafOfModules.sheafRingDerivedHomComparison.{u + 2, u + 1, u + 1, u} a
    (reductionChange T a) (reductionChange_obj_eq T a) (reductionChange_map_eq T a)
    (pbcScalarAdjunction a) (reductionDerivedChange T a) (reductionDerivedCounit T a)
    (reductionDerivedUniversal T a)
  have hc := CategoryTheory.adjunction_cochain_transpose
    (reductionChange T a) (reductionRestrict T a) (pbcScalarAdjunction a)
    (reductionDerivedChange T a)
    (complexCounitNat (reductionChange T a) (reductionDerivedChange T a)
      (reductionDerivedCounit T a)) (reductionDerivedCounit T a)
    (fun P ↦ by
      simp only [complexCounitNat_app]
      have hi : (DerivedCategory.quotientCompQhIso (reductionModules T R)).hom.app P =
          𝟙 _ := rfl
      have hh : (DerivedCategory.quotientCompQhIso (reductionModules T S)).hom.app
          (((reductionChange T a).mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
      rw [hi, hh]
      erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
      exact (finiteCounit_eq (reductionChange T a) (reductionDerivedChange T a)
        (reductionDerivedCounit T a) P).symm) ad had
  have he : ad = pbcDerivedScalarAdjunction a := by
    unfold pbcDerivedScalarAdjunction
    with_unfolding_all
      apply (pbcDerivedScalarAdjunction_exists a).unique ?_
        (pbcDerivedScalarAdjunction_exists a).exists.choose_spec
      intro P hP
      have hu := hc P (((reductionChange T a).mapHomologicalComplex (.up ℤ)).obj P) (𝟙 _)
      erw [DerivedCategory.Q.map_id, Category.comp_id, Adjunction.homEquiv_id] at hu
      have hv := congrArg (fun f ↦ f ≫ (reductionRestrict T a).mapDerivedCategoryFactors.hom.app
        (((reductionChange T a).mapHomologicalComplex (.up ℤ)).obj P)) hu
      simp only [Category.assoc, Iso.inv_hom_id_app] at hv
      change ad.unit.app _ ≫ _ ≫ _ = _
      simp only [complexCounitNat_app, Adjunction.homEquiv_unit] at hv
      have hv' := hv.trans (Category.comp_id _)
      exact (Category.assoc _ _ _).symm.trans hv'
  rw [he] at hc
  intro P K f
  have hh := hc P K f
  erw [complexCounitNat_app] at hh
  simpa only [pbcComplexCounit, pbcExtensionCounit, reductionComplexCounit,
    pbcExtend, pbcDerivedExtend, pbcModules, reductionModules, pbcDerivedRestrict,
    pbcRestrict, proEtaleRingRestrictScalars, reductionRestrict] using hh

private theorem finiteMate_computed (n : ℕ)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{0} _) (ProEt.topology Y)
      (pbcAdicCompletion Y d) P) :
    (finiteMate g d n).app (DerivedCategory.Q.obj P) ≫
        completedReductionFiniteModelMap g d n P =
      (reductionDerivedChange X (completedReductionProjection X d n)).map
          (completedOrdinaryPullbackComplexCounit g d P) ≫
        pbcComplexCounit (completedReductionProjection X d n)
          (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (ordinaryFiniteMate g d n) (.up ℤ)).app P) := by
  with_unfolding_all
    let φ := completedReductionProjection X d n
    let P' := ((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P
    let S := (((completedReductionFiniteModules g d n).mapHomologicalComplex (.up ℤ)).obj
      (((reductionChange Y (completedReductionProjection Y d n)).mapHomologicalComplex
        (.up ℤ)).obj P))
    let m := (NatTrans.mapHomologicalComplex (ordinaryFiniteMate g d n) (.up ℤ)).app P
    have hm : ((pbcScalarAdjunction φ).mapHomologicalComplex (.up ℤ)).homEquiv P' S m =
        (NatTrans.mapHomologicalComplex (ordinaryFiniteAugmentation g d n) (.up ℤ)).app P := by
      apply HomologicalComplex.hom_ext
      intro i
      change ((pbcScalarAdjunction φ).homEquiv _ _)
        (((pbcScalarAdjunction φ).homEquiv _ _).symm _) = _
      exact Equiv.apply_symm_apply _ _
    apply ((pbcDerivedScalarAdjunction φ).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right]
    dsimp only [finiteMate]
    rw [transpose_symm_app, Equiv.apply_symm_apply]
    change (finiteAugmentation g d n).app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedRestrict φ).map (completedReductionFiniteModelMap g d n P) = _
    rw [Adjunction.homEquiv_naturality_left]
    erw [finiteCanonicalTranspose X φ P' S m, hm]
    apply (cancel_mono ((pbcRestrict φ).mapDerivedCategoryFactors.hom.app S)).mp
    simp only [pbcRestrict, proEtaleRingRestrictScalars, reductionRestrict,
      Category.assoc, Iso.inv_hom_id_app]
    exact finiteAugmentation_computed g d n P hP

private theorem finiteMate_isIso_on_model (n : ℕ)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{0} _) (ProEt.topology Y)
      (pbcAdicCompletion Y d) P)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology Y) (R := pbcAdicCompletion Y d) (P.X i)) :
    IsIso ((finiteMate g d n).app (DerivedCategory.Q.obj P)) := by
  with_unfolding_all
    let P' := ((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P
    have hp' : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        X.ProEt inferInstance (essentiallySmallSelf.{0} _) (ProEt.topology X)
        (pbcAdicCompletion X d) P' := by
      simpa only [P', completedModulePullback_eq_exact] using
        (finitePullback_good g _ _ (d.integralRingIso g) P hP hflat).1
    have : IsIso ((completedOrdinaryPullbackCounit g d).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
      unfold completedOrdinaryPullback completedOrdinaryPullbackCounit
      exact (completedOrdinaryPullback_exists g d).choose_spec.choose_spec.2 P hP
    have : IsIso (completedOrdinaryPullbackComplexCounit g d P) := by
      unfold completedOrdinaryPullbackComplexCounit Functor.leftDerivedCounitOnComplex
      infer_instance
    have : IsIso (pbcComplexCounit (completedReductionProjection X d n) P') := by
      have := pbcExtensionCounit_isIso (completedReductionProjection X d n) P' hp'
      unfold pbcComplexCounit
      infer_instance
    let : ∀ i : ℤ, IsIso
        (((NatTrans.mapHomologicalComplex (ordinaryFiniteMate g d n) (.up ℤ)).app P).f i) :=
      fun i ↦ NatIso.isIso_app_of_isIso (ordinaryFiniteMate g d n) (P.X i)
    have : IsIso ((NatTrans.mapHomologicalComplex
        (ordinaryFiniteMate g d n) (.up ℤ)).app P) :=
      HomologicalComplex.Hom.isIso_of_components _
    have : IsIso ((finiteMate g d n).app (DerivedCategory.Q.obj P) ≫
        completedReductionFiniteModelMap g d n P) := by
      rw [finiteMate_computed g d n P hP]
      infer_instance
    have := completedReductionFiniteModelMap_isIso g d n P hP
    exact IsIso.of_isIso_comp_right _ (completedReductionFiniteModelMap g d n P)

/-- The finite mate of the pulled quotient augmentation is invertible.
Source: Stacks Tag 099N (5), normalized finite pullback comparison.
(blueprint: lem-weil-pbc-completed-pullback-finite-mate).

Proof: compose the actual limit projection with the constant-limit unit and the
pulled quotient augmentation. Naturality of the derived limit projection and the
constant-limit adjunction triangle identify this composite with evaluation of the
augmentation. On a flat K-flat representative, the normalized finite comparison
sends this map to the quotient scalar unit followed by the ordinary finite
pullback tensor comparison. The latter is an isomorphism by associativity of
extension of scalars. Transpose through the finite scalar adjunction and descend
through the universal derived counits. -/
theorem completedPullbackComparison_finiteMate_isIso
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) (n : ℕ) :
    IsIso ((reductionDerivedChange X (completedReductionProjection X d n)).map
        (completedPullbackComparison g d K) ≫ completedPullbackReductionArrow g d K n) := by
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let P₀ := DerivedCategory.Q.objPreimage K
  obtain ⟨P, p, hP, hflat, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := pbcAdicCompletion Y d) P₀
  have := hp
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have hflat' (i : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology Y) (R := pbcAdicCompletion Y d) (P.X i) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (pbcAdicCompletion Y d) (P.X i)).symm (hflat i)
  have := finiteMate_isIso_on_model g d n P hP hflat'
  have hn := (finiteMate g d n).naturality e.hom
  have : IsIso ((finiteMate g d n).app K) := by
    have : IsIso (((completedOrdinaryPullback g d) ⋙
        reductionDerivedChange X (completedReductionProjection X d n)).map e.hom ≫
          (finiteMate g d n).app K) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_left
      (((completedOrdinaryPullback g d) ⋙
        reductionDerivedChange X (completedReductionProjection X d n)).map e.hom)
      ((finiteMate g d n).app K)
  rw [← finiteMate_app g d K n]
  infer_instance

end AlgebraicGeometry.Scheme
