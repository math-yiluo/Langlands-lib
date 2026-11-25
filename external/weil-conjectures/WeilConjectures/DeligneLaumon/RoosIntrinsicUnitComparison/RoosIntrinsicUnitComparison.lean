/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.PrincipalIntrinsicCompletion.PrincipalIntrinsicCompletion
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosModel
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.CategoryTheory.Abelian.FunctorCategory
import all WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.DeligneLaumon.QuotientTensorScalarTowerComparison
import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import all WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # The normalized Roos and intrinsic Koszul units agree

Source: Stacks Project, Tags 099M and 0941; Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-a1-roos-intrinsic-unit-comparison).
The maps are specified on chain coordinates, including the zero shifted components.
A total derived limit is evaluated on any K-injective strict-tower resolution; its
comparison is normalized by the actual ordinary-limit inclusion, not just its projections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

namespace WeilConjectures.RoosIntrinsicUnitComparison
open PrincipalKoszulStrictReplacement PrincipalIntrinsicCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : AlgebraicGeometry.Scheme.{t})

/-- The actual strict quotient tensor tower, assembled in the tower category.
Source: Stacks 099M (blueprint: lem-a1-roos-intrinsic-unit-comparison). -/
abbrev quotientTower (P : CochainComplex (Modules l E W) ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ Modules l E W) ℤ :=
  koszulTowerComplex (completedIntegralCommRingSheafUnrestricted l E W) (targetTower l E W P)

/-- The independent quotient unit, obtained by tensoring the specified limit projection.
Source: Stacks 099M (blueprint: lem-a1-roos-intrinsic-unit-comparison). -/
def quotientUnit (P : CochainComplex (Modules l E W) ℤ) (n : ℕ) :
    P ⟶ (targetTower l E W P).obj (op n) :=
  (tensorUnit l E W P).inv ≫ (tensorWith l E W P).map
    ((CochainComplex.singleFunctor (Modules l E W) 0).map (projection l E W n))

section Helpers
attribute [local instance 3000] integralCompletedRingHasDerivedCategory
  integralOperationsCountableProducts
attribute [local implicit_reducible] integralTowerHasDerivedCategory
  integralCompletedRingHasDerivedCategory IntegralOnSlice.hasDerived
attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose
  IntegralOnSlice.Site IntegralOnSlice.siteCategory IntegralOnSlice.topology
  IntegralOnSlice.restrict IntegralOnSlice.ring IntegralOnSlice.Good
  IntegralOnSlice.qGood IntegralOnSlice.roosGood
  integralOperationsGoodComplex integralOperationsRoosFunctor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible]
  completedIntegralCoefficientSheafUnrestricted
  SheafOfModules.unit SheafOfModules.monoidalCategory
  PresheafOfModules.sheafificationAdjunction HasDerivedCategory.standard

attribute [local implicit_reducible] SheafOfModules.instAbelian
  abelianOfAdjunction Abelian.ofCoimageImageComparisonIsIso

private abbrev ComparisonModules := Modules l E W

section
attribute [local implicit_reducible] ComplexShape.up ComplexShape.up'
  CochainComplex.mappingCone
end

private theorem transport_unit
    {D : Type*} [Category* D] {X F I U : D}
    (e : F ≅ U) (c : I ≅ U) (ι : X ⟶ I) (υ : X ⟶ U) (α : X ⟶ F)
    (hι : ι ≫ c.hom = υ) (hα : α ≫ e.hom = υ) :
    α ≫ (e ≪≫ c.symm).hom = ι := by
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc]
  exact c.comp_inv_eq.mpr (hα.trans hι.symm)

private theorem unit_compatible_of_comparison
    {B : Type*} [Category* B] {P X X' Y Y' : B}
    (u : P ⟶ X) (u' : P ⟶ X') (v : P ⟶ Y) (v' : P ⟶ Y')
    (a : X ⟶ Y) (a' : X' ⟶ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : u ≫ a = v) (h' : u' ≫ a' = v')
    (hn : f ≫ a' = a ≫ g) (hu : u ≫ f = u') : v ≫ g = v' := by
  calc
    v ≫ g = (u ≫ a) ≫ g := congrArg (fun z ↦ z ≫ g) h.symm
    _ = (u ≫ f) ≫ a' := by rw [Category.assoc, ← hn, ← Category.assoc]
    _ = v' := (congrArg (fun z ↦ z ≫ a') hu).trans h'

section ConcreteInstances
set_option backward.isDefEq.respectTransparency true
variable [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}]

section UnitCompatibility
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] tensorUnit tensorWith
attribute [local implicit_reducible] sourceTower targetTower comparison levelUnit quotientUnit
  koszulTowerComplex koszulTowerComplexMap principalKoszulTower principalKoszul
  Functor.ofOpSequence Functor.ofSequence

omit [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private theorem levelUnit_compatible (P : CochainComplex (Modules l E W) ℤ) (n : ℕ) :
    levelUnit l E W P (n + 1) ≫
        (tower l E W P).asFunctor.map (homOfLE n.le_succ).op = levelUnit l E W P n := by
  dsimp only [levelUnit]
  change ((tensorUnit l E W P).inv ≫ (tensorWith l E W P).map _) ≫
    (tensorWith l E W P).map _ = _
  erw [Category.assoc, ← Functor.map_comp]
  apply congrArg ((tensorUnit l E W P).inv ≫ ·)
  apply congrArg (tensorWith l E W P).map
  dsimp only [principalKoszulTower]
  erw [Functor.ofOpSequence_map_homOfLE_succ]
  dsimp only [principalKoszulTransition, CochainComplex.mappingCone.map]
  erw [CochainComplex.mappingCone.inr_desc]
  exact Category.id_comp _

omit [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private theorem levelUnit_comparison (P : CochainComplex (Modules l E W) ℤ) (n : ℕ) :
    levelUnit l E W P n ≫ (comparison l E W P).app (op n) =
      quotientUnit l E W P n := by
  change ((tensorUnit l E W P).inv ≫ (tensorWith l E W P).map _) ≫
    (tensorWith l E W P).map _ = _
  dsimp only [quotientUnit]
  erw [Category.assoc, ← Functor.map_comp]
  apply congrArg ((tensorUnit l E W P).inv ≫ ·)
  apply congrArg (tensorWith l E W P).map
  let F := CochainComplex.singleFunctor (Modules l E W) 0
  let a := multiplication l E W n
  let S : ShortComplex (CochainComplex (Modules l E W) ℤ) :=
    ShortComplex.mk (F.map a) (F.map (cokernel.π a)) (by
      erw [← F.map_comp, cokernel.condition, F.map_zero])
  have h := CochainComplex.mappingCone.inr_descShortComplex S
  change CochainComplex.mappingCone.inr (F.map a) ≫
    (CochainComplex.mappingCone.descShortComplex S ≫ F.map (quotientComparison l E W n)) = _
  erw [← Category.assoc, h, ← F.map_comp]
  dsimp only [quotientComparison]
  erw [cokernel.π_desc]

omit [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private theorem quotientUnit_compatible (P : CochainComplex (Modules l E W) ℤ) (n : ℕ) :
    quotientUnit l E W P (n + 1) ≫
        (quotientTower l E W P).asFunctor.map (homOfLE n.le_succ).op =
      quotientUnit l E W P n := by
  exact unit_compatible_of_comparison
    (levelUnit l E W P (n + 1)) (levelUnit l E W P n)
    (quotientUnit l E W P (n + 1)) (quotientUnit l E W P n)
    ((comparison l E W P).app (op (n + 1))) ((comparison l E W P).app (op n))
    ((sourceTower l E W P).map (homOfLE n.le_succ).op)
    ((targetTower l E W P).map (homOfLE n.le_succ).op)
    (levelUnit_comparison l E W P (n + 1)) (levelUnit_comparison l E W P n)
    ((comparison l E W P).naturality (homOfLE n.le_succ).op)
    (levelUnit_compatible l E W P n)

end UnitCompatibility

section RoosTowerComparisonAPI
attribute [local irreducible] roosF DerivedCategory DerivedCategory.Q

end RoosTowerComparisonAPI

private def quotientAugmentation (P : CochainComplex (Modules l E W) ℤ) :
    P ⟶ roosF.obj (quotientTower l E W P) :=
  roosAugment (quotientUnit l E W P) (quotientUnit_compatible l E W P)

section
set_option backward.isDefEq.respectTransparency false
variable {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
attribute [local implicit_reducible]
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
attribute [local implicit_reducible] integralOperationsTowerStep integralOperationsRoos

private theorem roosMap_eq {X Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} (f : X ⟶ Y) :
    roosF.map f = integralOperationsRoosMap
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) := by
  unfold integralOperationsRoosMap
  rw [arrowConeMap B _ _ _ _ (integralOperationsRoos_square
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f))]
  rfl

section RingedRoos
universe c v r
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasCountableProducts (SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]

end RingedRoos

attribute [local irreducible] targetTower IntegralOnSlice.tower IntegralOnSlice.augmentation

section OrdinaryWrapperAPI
attribute [local semireducible] targetTower
attribute [local implicit_reducible] targetTower Functor.ofOpSequence Functor.ofSequence
attribute [local irreducible] tensorWith tensorUnit

-- These wrappers keep the module category in their types while using the slice constructions.
private def ordinaryTower : CochainComplex (ComparisonModules l E W) ℤ ⥤
    (ℕᵒᵖ ⥤ CochainComplex (ComparisonModules l E W) ℤ) :=
  IntegralOnSlice.tower l E W none

private def ordinaryAugmentation :
    (Functor.const ℕᵒᵖ : CochainComplex (ComparisonModules l E W) ℤ ⥤
      (ℕᵒᵖ ⥤ CochainComplex (ComparisonModules l E W) ℤ)) ⟶ ordinaryTower l E W :=
  IntegralOnSlice.augmentation l E W none

end OrdinaryWrapperAPI

section ScalarRoosComparison
set_option backward.isDefEq.respectTransparency true
attribute [local implicit_reducible] roosConeFunctor CochainComplex.mappingCocone
  IntegralOnSlice.roos quotientAugmentation koszulTowerComplex koszulTowerComplexMap
attribute [local irreducible] CochainComplex.mappingCone roosF

end ScalarRoosComparison

end

omit [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private theorem good_representative (K : IntegralOnSlice.D l E W none) :
    ∃ P : (IntegralOnSlice.Good l E W none).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  let q := IntegralOnSlice.qGood l E W none
  have : q.IsLocalization ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage
      (IntegralOnSlice.Good l E W none).ι) := IntegralOnSlice.goodLocalization l E W none
  have := Localization.essSurj q
    ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage
      (IntegralOnSlice.Good l E W none).ι)
  exact ⟨q.objPreimage K, ⟨q.objObjPreimageIso K⟩⟩

omit [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private lemma good_shift (P : CochainComplex (integralTowerModules l E W) ℤ)
    (hP : integralOperationsGoodComplex l E W P) (m : ℤ) :
    integralOperationsGoodComplex l E W (P⟦m⟧) := by
  refine ⟨?_, fun i ↦ hP.2 (i + m)⟩
  exact SheafOfModules.KFlatFixedTensor.shift_kFlat
    (completedIntegralCommRingSheafUnrestricted l E W) P hP.1 m

attribute [local irreducible] IntegralOnSlice.completion
  IntegralOnSlice.completionComparison IntegralOnSlice.completionUnit

section QuotientDescentAPI
attribute [local irreducible] roosF DerivedCategory DerivedCategory.Q

end QuotientDescentAPI

end ConcreteInstances

attribute [local implicit_reducible] koszulTowerComplex koszulTowerComplexMap
  roosF roosConeFunctor CochainComplex.mappingCocone fiber quotientAugmentation
attribute [local irreducible] CochainComplex.mappingCone roosχ
attribute [local irreducible] sourceTower targetTower tensorWith sourceTowerMap targetTowerMap
  comparison levelUnit quotientUnit tensorUnit

attribute [local irreducible] roosF
attribute [local irreducible] roosAugment roosLift limit DerivedCategory DerivedCategory.Q

-- Checking all strict coordinates and natural comparison squares needs extra heartbeats.
end Helpers

end WeilConjectures.RoosIntrinsicUnitComparison
