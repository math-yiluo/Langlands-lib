/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.CategoryTheory.ConstantModuleFlat
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.Algebra.Homology.FlatTermKFlatFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Mathlib.Algebra.Category.ModuleCat.AB

/-! Constant realization preserves flat-term K-flat complexes on arbitrary sites. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject

namespace CategoryTheory

private theorem constantModule_colimits
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Type (max u v)) [CommRing R] :
    PreservesColimitsOfSize.{0, 0} (commutativeSiteConstantModuleFunctor J R) := by
  let : HasSheafify J AddCommGrpCat.{max u v} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u v} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
  let P := siteConstantModulePresheafGeneral (C := C) R
  have : PreservesColimitsOfSize.{0, 0} P := by
    constructor
    intro K _
    constructor
    intro D
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun _ ↦ hc)⟩
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  change PreservesColimitsOfSize.{0, 0}
    (P ⋙ PresheafOfModules.sheafification.{max u v} (realizationRingUnit J R))
  infer_instance

/-- Constant realization preserves K-flat complexes whose terms are flat.
Source: Stacks Project, Tag 0G7E
(blueprint: lem-sfb-constant-module-kflat).
Proof: constant module presheaves preserve colimits by evaluation, and module
sheafification is a left adjoint. Constant realization preserves flat objects by
the local relation criterion. Apply preservation of flat-term K-flat complexes
by additive functors preserving flat objects and integer-indexed colimits. The
categorical K-flat conclusion implies that tensoring any acyclic complex with
the realized complex is acyclic by applying it to the quasi-isomorphism 0 → Z.
This uses neither a terminal site object nor enough points. -/
theorem isKFlat_constantModule
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Type (max u v)) [CommRing R] (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hP : P.IsKFlatForTotalTensor) (hf : ∀ i, Module.Flat R (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := realizationRing J R)
      (((commutativeSiteConstantModuleFunctor J R).mapHomologicalComplex (.up ℤ)).obj P) := by
  let : HasSheafify J AddCommGrpCat.{max u v} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u v} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
  let O := realizationRing J R
  let A := realizationModules J R
  let F := commutativeSiteConstantModuleFunctor J R
  let := SheafOfModules.isMonoidal_W_independentCoefficients O
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := SheafOfModules.tensorPreadditive O
  let := SheafOfModules.monoidalClosed_kfi (R := O)
  have : IsGrothendieckAbelian.{max u v} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      J O).1
  have : F.PreservesFlat := ⟨fun hM ↦ SheafOfModules.flat_to_cat O _
    (isFlatOnSite_constantModule J R _ ((ModuleCat.flat_iff_flat _).1 hM))⟩
  have : PreservesColimitsOfSize.{0, 0} F := constantModule_colimits J R
  have hp : (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat P := hP
  have hk := F.kFlat_map_of_flat_terms P hp
    (fun i ↦ (ModuleCat.flat_iff_flat _).2 (hf i))
  intro Z hZ
  -- Supply the graded tensor instances explicitly; the monoidal structure on complexes is
  -- otherwise not found by instance search here.
  have : ∀ X Y : GradedObject ℤ A, X.HasTensor Y := inferInstance
  have : ∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂) :=
    inferInstance
  have : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ :=
    inferInstance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ :=
    inferInstance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ :=
    inferInstance
  let T := MonoidalCategory.tensorRight ((F.mapHomologicalComplex (.up ℤ)).obj P)
  have hz : QuasiIso (0 : (0 : CochainComplex A ℤ) ⟶ Z) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt _ i
      ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
  have hmap : QuasiIso (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) := hk.2 _ hz
  have htzero : (T.obj (0 : CochainComplex A ℤ)).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
  exact fun i ↦ (exactAt_iff_of_quasiIsoAt
    (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) i).1 (htzero i)

end CategoryTheory
