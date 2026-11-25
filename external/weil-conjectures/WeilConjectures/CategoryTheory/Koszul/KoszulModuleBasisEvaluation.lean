/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Strict.StrictScalarKoszulInstances
import all WeilConjectures.CategoryTheory.RingedHomTensorUnitNormalization
import all WeilConjectures.CategoryTheory.RingedComplexTensorEvaluation
import all WeilConjectures.CategoryTheory.RingedKoszulSystem
import all WeilConjectures.CategoryTheory.RingedExtendedCech
import all WeilConjectures.CategoryTheory.RingedSectionLocalization
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.RingTheory.Localization.Away.Basic
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Homology.HomComplex
import all WeilConjectures.CategoryTheory.RingedCompletionUnit
import all WeilConjectures.CategoryTheory.RingedDerivedRestriction
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import all WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import all Mathlib.Algebra.Homology.Double
import all Mathlib.CategoryTheory.Endomorphism
import all WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import all Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.Algebra.Homology.Monoidal.Dual

/-! # KoszulModuleBasisEvaluation for strict Koszul comparison

Source: Stacks Project, Tags 0A0E and 0913.
(blueprint: lem-f5-koszul-module-basis-evaluation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FlatScalarKoszul

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable {R B : Sheaf J CommRingCat.{u}}

open MonoidalCategory
open scoped CategoryTheory.Prod

attribute [local irreducible] homComplexFunctor
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  Localization.Monoidal.tensorBifunctor

attribute [local instance] gradedTensorCache gradedGoodTensorLeftCache
  gradedGoodTensorRightCache gradedFourCache tensorPreservesEmptyLeftCache
  tensorPreservesEmptyRightCache cachedModuleMonoidal cachedModuleSymmetric
  cachedModulePreadditive cachedModuleClosed cachedComplexMonoidal
  cachedComplexBraided cachedComplexClosed

private theorem uncurry_units_smul {D : Type*} [Category D] [Preadditive D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
    {P Q T : D} (s : ℤˣ) (f : Q ⟶ (ihom P).obj T) :
    MonoidalClosed.uncurry (s • f) = s • MonoidalClosed.uncurry f := by
  simp only [MonoidalClosed.uncurry_eq, Units.smul_def]
  change (tensorLeft P).map ((s : ℤ) • f) ≫ _ = _
  rw [Functor.map_zsmul, Preadditive.zsmul_comp]
  rfl

private def evaluationUncurryCore {D : Type*} [Category D] [MonoidalCategory D]
    [BraidedCategory D] [MonoidalClosed D] (P N : D) :
    P ⊗ (N ⊗ (ihom P).obj (𝟙_ D)) ⟶ N :=
  P ◁ (β_ N ((ihom P).obj (𝟙_ D))).hom ≫
    (α_ P _ N).inv ≫ (ihom.ev P).app (𝟙_ D) ▷ N ≫ (λ_ N).hom

private theorem evaluationCurryCore {D : Type*} [Category D] [MonoidalCategory D]
    [BraidedCategory D] [MonoidalClosed D] (P N : D) :
    (β_ N ((ihom P).obj (𝟙_ D))).hom ≫ MonoidalClosed.ihomUnitTensorToIhom P N =
      MonoidalClosed.curry (evaluationUncurryCore P N) := by
  unfold evaluationUncurryCore MonoidalClosed.ihomUnitTensorToIhom
  rw [← MonoidalClosed.curry_natural_left]

private theorem curryEvaluationCore {D : Type*} [Category D] [MonoidalCategory D]
    [MonoidalClosed D] (P N : D) :
    MonoidalClosed.curry ((ihom.ev P).app N) = 𝟙 ((ihom P).obj N) := by
  rw [← MonoidalClosed.uncurry_id_eq_ev, MonoidalClosed.curry_uncurry]

private theorem signedUncurryInverse {D : Type*} [Category D] [Preadditive D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
    {P X Y : D} (s : ℤˣ) (a : X ⟶ (ihom P).obj Y) (f : P ⊗ X ⟶ Y)
    (h : a = s • MonoidalClosed.curry f) : f = s • MonoidalClosed.uncurry a := by
  have h' := congrArg MonoidalClosed.uncurry h
  rw [uncurry_units_smul, MonoidalClosed.uncurry_curry] at h'
  rw [h', smul_smul, Int.units_mul_self, one_smul]

-- Elaborate the tensor and Hom comparison through their explicit site instances.
private theorem complexEvaluation_component (O : Sheaf J CommRingCat.{u})
    (P N : ringedSiteComplex O) (p q n : ℤ) (h : p + q = n) :
    let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
    let := cachedModuleMonoidal O
    let := cachedModuleSymmetric O
    let := cachedModulePreadditive O
    let := cachedModuleClosed O
    let := cachedComplexClosed O
    HomologicalComplex.ιTensorObj P (homComplex (R := O) P N) p q n h ≫
        ((ihom.ev P).app N).f n =
      (p * q).negOnePow • MonoidalClosed.uncurry (homComplexπ P N q p n h) := by
  let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  let := cachedModuleMonoidal O
  let := cachedModuleSymmetric O
  let := cachedModulePreadditive O
  let := cachedModuleClosed O
  let := cachedComplexClosed O
  dsimp only
  have hc := ringedComplexCurry_component O ((ihom.ev P).app N) q p n h
  rw [curryEvaluationCore, HomologicalComplex.id_f, Category.id_comp] at hc
  exact signedUncurryInverse (p * q).negOnePow _ _ hc

private theorem moduleCurry (O : Sheaf J CommRingCat.{u})
    {P X Y : Modules O} (g : ((tensor O).obj P).obj X ⟶ Y) :
    let := SheafOfModules.monoidalCategory O
    let := Classical.choice (SheafOfModules.tensorClosed O).1
    let := SheafOfModules.monoidalClosed (R := O)
    MonoidalClosed.curry g = SheafOfModules.tensorHomEquiv P X Y g := by
  let := SheafOfModules.monoidalCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := SheafOfModules.monoidalClosed (R := O)
  dsimp only
  apply MonoidalClosed.uncurry_injective
  erw [MonoidalClosed.uncurry_curry]

private theorem moduleHomMap (O : Sheaf J CommRingCat.{u})
    (P X Y : Modules O) (f : X ⟶ Y) :
    let := cachedModuleMonoidal O
    let := cachedModuleClosed O
    (ihom P).map f = SheafOfModules.homObjMap (R := O) (𝟙 P) f := by
  rfl

private theorem homPostBasis (O : Sheaf J CommRingCat.{u}) {P X Y : Modules O}
    (b : one O ⟶ P) (f : X ⟶ Y) :
    SheafOfModules.homObjMap (R := O) (𝟙 P) f ≫
        SheafOfModules.homObjMap (R := O) b (𝟙 Y) ≫
        (SheafOfModules.homObjUnitIso (R := O) Y).hom =
      SheafOfModules.homObjMap (R := O) b f ≫
        (SheafOfModules.homObjUnitIso (R := O) Y).hom := by
  have h := SheafOfModules.homObjMap_comp_homObjMap (R := O) (𝟙 P) b f (𝟙 Y)
  have h' : SheafOfModules.homObjMap (R := O) (𝟙 P) f ≫
      SheafOfModules.homObjMap (R := O) b (𝟙 Y) =
        SheafOfModules.homObjMap (R := O) b f := by
    simpa only [Category.comp_id] using h
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun z ↦ z ≫ (SheafOfModules.homObjUnitIso (R := O) Y).hom) h')

private theorem homUnit_natural (O : Sheaf J CommRingCat.{u})
    {X Y : Modules O} (f : X ⟶ Y) :
    SheafOfModules.homObjMap (R := O) (𝟙 (one O)) f ≫
        (SheafOfModules.homObjUnitIso (R := O) Y).hom =
      (SheafOfModules.homObjUnitIso (R := O) X).hom ≫ f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

private theorem curryUnit (O : Sheaf J CommRingCat.{u}) {X Y : Modules O}
    (g : ((tensor O).obj (one O)).obj X ⟶ Y) :
    let := SheafOfModules.monoidalCategory O
    let := Classical.choice (SheafOfModules.tensorClosed O).1
    let := SheafOfModules.monoidalClosed (R := O)
    MonoidalClosed.curry g ≫ (SheafOfModules.homObjUnitIso (R := O) Y).hom =
      (λ_ X).inv ≫ g := by
  let := SheafOfModules.monoidalCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := SheafOfModules.monoidalClosed (R := O)
  dsimp only
  have hg : g = (λ_ X).hom ≫ ((λ_ X).inv ≫ g) := by simp
  rw [moduleCurry]
  conv_lhs => rw [hg]
  erw [SheafOfModules.tensorHomEquiv_comp_homObjMap (R := O), Category.assoc,
    homUnit_natural, ← Category.assoc, ← moduleCurry,
    CategoryTheory.sheaf_unit O X, Category.id_comp]

/-- Evaluate the curry of a sheaf tensor map on a unit basis vector.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
Proof step 1: Identify categorical curry with the actual sheaf tensorHomEquiv by applying uncurry
injectivity. On sections, evaluation Hom(unit,Y) is natural in Y. Write any map unit tensor X to
Y as its left-unitor factorization; tensorHomEquiv naturality and the existing sheaf-unit
normalization identify its curry followed by unit evaluation with that factorization.
Proof step 2: Apply tensorHomEquiv naturality for precomposition by b and then the unit case.
This gives the displayed curryBasis formula.
Proof step 3: For cochain evaluation use the existing signed curry-component formula on the
evaluation map. Curry of evaluation is the identity. Apply uncurry and cancel the square of the
integer sign to get the evaluation component identity.
(blueprint: lem-f5-koszul-module-basis-evaluation). -/
theorem curryBasis (O : Sheaf J CommRingCat.{u}) {P X Y : Modules O}
    (b : one O ⟶ P) (g : ((tensor O).obj P).obj X ⟶ Y) :
    let := SheafOfModules.monoidalCategory O
    let := Classical.choice (SheafOfModules.tensorClosed O).1
    let := SheafOfModules.monoidalClosed (R := O)
    MonoidalClosed.curry g ≫ SheafOfModules.homObjMap (R := O) b (𝟙 Y) ≫
        (SheafOfModules.homObjUnitIso (R := O) Y).hom =
      (λ_ X).inv ≫ b ▷ X ≫ g := by
  let := SheafOfModules.monoidalCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := SheafOfModules.monoidalClosed (R := O)
  dsimp only
  erw [← Category.assoc, moduleCurry,
    ← SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := O) b g, ← moduleCurry]
  simpa only [Category.assoc] using curryUnit O (b ▷ X ≫ g)

end CategoryTheory.FlatScalarKoszul
