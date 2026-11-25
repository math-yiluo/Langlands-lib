/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
public import WeilConjectures.CategoryTheory.ProperBaseChange.LocalizationInverseImageCoherence
public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
public import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorCompositionUnit
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Data for localized ordinary pullback normalization

## References

* Bhatt--Scholze, Remark 6.8.15
* Stacks 099M
* Stacks 06YY
* Stacks 03D2
* Stacks 03EL, 0D6D, 07A4
* Stacks 03CB
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.LocalizedOrdinary

universe v w

local instance restrictedTargetSMul
    {D : Type v} [Category.{w} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A : Sheaf K CommRingCat.{u}}
    (M : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj A))
    {U V : Dᵒᵖ} (f : U ⟶ V) :
    SMul (A.obj.obj V)
      ((ModuleCat.restrictScalars
        (((sheafCompose K (forget₂ CommRingCat RingCat)).obj A).obj.map f).hom).obj
          (M.val.obj V)) :=
  (M.val.obj V).isModule.toSMul

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual completed coefficient sheaf B. -/
abbrev B (X : Scheme.{u}) : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  pbcAdicCompletion X (pbcIntegralDatum l E)

variable (ϖ : PbcIntegralRing l E)

/-- The constant chosen uniformizer section. -/
def uniformizer (X : Scheme.{u}) :
    ((B l E X).obj ⋙ CategoryTheory.forget CommRingCat.{u + 1}).sections :=
  pbcCompletedScalarSections X (pbcIntegralDatum l E) ϖ

attribute [-instance] WeilConjectures.integralCoefficientRingSheafify in
/-- The actual sheaf localization B[1/varpi]. -/
abbrev R (X : Scheme.{u}) : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  ringedLocalizationRingOfUniverses.{u + 1, u + 1, u} (B l E X) (uniformizer l E ϖ X)

attribute [-instance] WeilConjectures.integralCoefficientRingSheafify in
/-- The localization unit. -/
abbrev iota (X : Scheme.{u}) :=
  ringedLocalizationRingUnitOfUniverses.{u + 1, u + 1, u} (B l E X) (uniformizer l E ϖ X)

/-- Ordinary localization as actual scalar extension. -/
abbrev F₀ (X : Scheme.{u}) := pbcExtend (iota l E ϖ X)

/-- Unbounded derived scalar localization. -/
abbrev F (X : Scheme.{u}) := pbcDerivedExtend (iota l E ϖ X)

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The integral tensor-unit section, typed on the actual pulled-back chart.
This is the existing normalized adjunction unit, with no change in its data. -/
abbrev integralUnitSection (M : pbcModules X (B l E X)) (V : X.ProEt)
    (m : M.val.obj (op V)) :
    ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M).val.obj
      (op ((proEtaleBaseChange g).obj V)) :=
  pbcActualModuleUnitSection g (pbcIntegralDatum l E) M V m

/-- Ordinary ringed pullback along the localized structural map, without requiring it
invertible. -/
abbrev G₀ (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X) ⟶ R l E ϖ Y) :=
  proEtaleRingModulePullback g (R l E ϖ X)
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X)) (Iso.refl _) ⋙
      pbcExtend c

/-- Exact inverse image followed by derived scalar extension. -/
abbrev G (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X) ⟶ R l E ϖ Y) :=
  adicTowerPullback g (R l E ϖ X) ⋙ pbcDerivedExtend c

/-- Computation counit on arbitrary complexes. -/
def counit (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X) ⟶ R l E ϖ Y)
    (P : CochainComplex (pbcModules X (R l E ϖ X)) ℤ) :
    (G l E ϖ g c).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((G₀ l E ϖ g c).mapHomologicalComplex (.up ℤ)).obj P) :=
  (pbcDerivedExtend c).map
    ((proEtaleRingDerivedPullbackFactors g (R l E ϖ X)
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X))
        (Iso.refl _)).hom.app P) ≫
    pbcComplexCounit c
      (((proEtaleRingModulePullback g (R l E ϖ X)
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X))
          (Iso.refl _)).mapHomologicalComplex (.up ℤ)).obj P)

/-- The ordinary pullback tensor unit on a base-changed chart. -/
def unitSection
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X) ⟶ R l E ϖ Y)
    (M : pbcModules X (R l E ϖ X)) (V : X.ProEt) (m : M.val.obj (op V)) :=
  pbcTensorSection c
    ((proEtaleRingModulePullback g (R l E ϖ X)
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X))
        (Iso.refl _)).obj M) (op ((proEtaleBaseChange g).obj V)) 1
    (proEtaleRingModuleUnitSection g (R l E ϖ X)
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X))
        (Iso.refl _) M V m)

/-- A coefficient section pulled through the ring adjunction and structural map. -/
def scalarSection
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X) ⟶ R l E ϖ Y)
    (V : X.ProEt) (e : (R l E ϖ X).obj.obj (op V)) :=
  c.hom.app (op ((proEtaleBaseChange g).obj V))
    (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app (R l E ϖ X)).hom.app (op V) e)

/-- Data for the specified localization comparison. Its ring map is fixed by the
localization unit. Its ordinary comparison is fixed on tensor-unit generators,
and its derived comparison is fixed by the ordinary computation counits. -/
structure Edge where
  coefficient : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X) ⟶ R l E ϖ Y
  coefficient_unit : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (iota l E ϖ X) ≫
    coefficient = completedCoefficientMap g (pbcIntegralDatum l E) ≫ iota l E ϖ Y
  ordinary : pbcActualModulePull g (pbcIntegralDatum l E) ⋙ F₀ l E ϖ Y ≅
    F₀ l E ϖ X ⋙ G₀ l E ϖ g coefficient
  ordinary_unit : ∀ (M : pbcModules X (B l E X)) (V : X.ProEt)
    (m : M.val.obj (op V)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (pbcTensorSection (iota l E ϖ Y)
        ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
        (op ((proEtaleBaseChange g).obj V)) 1
        (integralUnitSection l E g M V m)) =
      unitSection l E ϖ g coefficient ((F₀ l E ϖ X).obj M) V
        (pbcTensorSection (iota l E ϖ X) M (op V) 1 m)
  ordinary_tensor : ∀ (M : pbcModules X (B l E X)) (V : X.ProEt)
    (m : M.val.obj (op V))
    (b : (B l E Y).obj.obj (op ((proEtaleBaseChange g).obj V)))
    (e : (R l E ϖ Y).obj.obj (op ((proEtaleBaseChange g).obj V))),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (pbcTensorSection (iota l E ϖ Y)
        ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
        (op ((proEtaleBaseChange g).obj V)) e
        (b • integralUnitSection l E g M V m)) =
    (e * (iota l E ϖ Y).hom.app (op ((proEtaleBaseChange g).obj V)) b) •
      unitSection l E ϖ g coefficient ((F₀ l E ϖ X).obj M) V
        (pbcTensorSection (iota l E ϖ X) M (op V) 1 m)
  ordinary_inverse_unit : ∀ (M : pbcModules X (B l E X)) (V : X.ProEt)
    (m : M.val.obj (op V))
    (e : (R l E ϖ Y).obj.obj (op ((proEtaleBaseChange g).obj V))),
    (ordinary.inv.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (e • unitSection l E ϖ g coefficient ((F₀ l E ϖ X).obj M) V
        (pbcTensorSection (iota l E ϖ X) M (op V) 1 m)) =
    pbcTensorSection (iota l E ϖ Y)
      ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
      (op ((proEtaleBaseChange g).obj V)) e
      (integralUnitSection l E g M V m)
  derived : pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙ F l E ϖ Y ≅
    F l E ϖ X ⋙ G l E ϖ g coefficient
  derived_model : ∀ P : CochainComplex (pbcModules X (B l E X)) ℤ,
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      X.ProEt inferInstance (essentiallySmallSelf.{0} _) (ProEt.topology X) (B l E X) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology X) (R := B l E X) (P.X n)) →
    derived.hom.app (DerivedCategory.Q.obj P) ≫
      (G l E ϖ g coefficient).map (pbcComplexCounit (iota l E ϖ X) P) ≫
      counit l E ϖ g coefficient
        (((F₀ l E ϖ X).mapHomologicalComplex (.up ℤ)).obj P) =
    (F l E ϖ Y).map (pbcActualPullComplexCounit g (pbcIntegralDatum l E) P) ≫
      pbcComplexCounit (iota l E ϖ Y)
        (((pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)

variable {Z : Scheme.{u}} (h : Z ⟶ Y)

/-- The composition comparisons with their rational tensor-generator value, inverse
unit insertion, and derived representative equation. The last equation is the
specified delta-compositor square on every unbounded derived object. -/
structure Composition (ag : Edge l E ϖ g) (ah : Edge l E ϖ h) (ac : Edge l E ϖ (h ≫ g)) where
  coefficient_comp : ac.coefficient =
    (proEtaleRingInverseImageComp h g).hom.app (R l E ϖ X) ≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map ag.coefficient ≫ ah.coefficient
  ordinary : G₀ l E ϖ g ag.coefficient ⋙ G₀ l E ϖ h ah.coefficient ≅
    G₀ l E ϖ (h ≫ g) ac.coefficient
  ordinary_tensor : ∀ (M : pbcModules X (R l E ϖ X)) (V : X.ProEt)
    (m : M.val.obj (op V))
    (e' : (R l E ϖ Y).obj.obj (op ((proEtaleBaseChange g).obj V)))
    (e'' : (R l E ϖ Z).obj.obj
      (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))),
    (ordinary.hom.app M).val.app
      (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
      (e'' • unitSection l E ϖ h ah.coefficient ((G₀ l E ϖ g ag.coefficient).obj M)
        ((proEtaleBaseChange g).obj V)
        (e' • unitSection l E ϖ g ag.coefficient M V m)) =
    (e'' * scalarSection l E ϖ h ah.coefficient ((proEtaleBaseChange g).obj V) e') •
      (show ((G₀ l E ϖ (h ≫ g) ac.coefficient).obj M).val.obj
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V))) from
        ((G₀ l E ϖ (h ≫ g) ac.coefficient).obj M).val.map
          ((MorphismProperty.Over.pullbackComp h g).inv.app V).op
          (unitSection l E ϖ (h ≫ g) ac.coefficient M V m))
  ordinary_inverse_unit : ∀ (M : pbcModules X (R l E ϖ X)) (V : X.ProEt)
    (m : M.val.obj (op V)),
    (ordinary.inv.app M).val.app
      (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
      (((G₀ l E ϖ (h ≫ g) ac.coefficient).obj M).val.map
        ((MorphismProperty.Over.pullbackComp h g).inv.app V).op
          (unitSection l E ϖ (h ≫ g) ac.coefficient M V m)) =
    unitSection l E ϖ h ah.coefficient ((G₀ l E ϖ g ag.coefficient).obj M)
      ((proEtaleBaseChange g).obj V) (unitSection l E ϖ g ag.coefficient M V m)
  derived : G l E ϖ g ag.coefficient ⋙ G l E ϖ h ah.coefficient ≅
    G l E ϖ (h ≫ g) ac.coefficient
  derived_model : ∀ P : CochainComplex (pbcModules X (R l E ϖ X)) ℤ,
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      X.ProEt inferInstance (essentiallySmallSelf.{0} _)
      (ProEt.topology X) (R l E ϖ X) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology X) (R := R l E ϖ X) (P.X n)) →
    derived.hom.app (DerivedCategory.Q.obj P) ≫ counit l E ϖ (h ≫ g) ac.coefficient P =
    (G l E ϖ h ah.coefficient).map (counit l E ϖ g ag.coefficient P) ≫
      counit l E ϖ h ah.coefficient
        (((G₀ l E ϖ g ag.coefficient).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)
  ordinary_square : ∀ M : pbcModules X (B l E X),
    (F₀ l E ϖ Z).map ((pbcActualModulePullCompIso h g (pbcIntegralDatum l E)).inv.app M) ≫
      ac.ordinary.hom.app M =
    ah.ordinary.hom.app ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M) ≫
      (G₀ l E ϖ h ah.coefficient).map (ag.ordinary.hom.app M) ≫
      ordinary.hom.app ((F₀ l E ϖ X).obj M)
  ordinary_mixed_tensor : ∀ (M : pbcModules X (B l E X)) (V : X.ProEt)
    (m : M.val.obj (op V))
    (b' : (B l E Y).obj.obj (op ((proEtaleBaseChange g).obj V)))
    (e'' : (R l E ϖ Z).obj.obj
      (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))),
    (((F₀ l E ϖ Z).map
        ((pbcActualModulePullCompIso h g (pbcIntegralDatum l E)).inv.app M) ≫
      ac.ordinary.hom.app M).val.app
      (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V))))
      (pbcTensorSection (iota l E ϖ Z)
        ((pbcActualModulePull h (pbcIntegralDatum l E)).obj
          ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M))
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V))) e''
        (integralUnitSection l E h
          ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
          ((proEtaleBaseChange g).obj V)
          (b' • integralUnitSection l E g M V m))) =
    (e'' * (iota l E ϖ Z).hom.app
      (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
      ((completedCoefficientMap h (pbcIntegralDatum l E)).hom.app
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
        (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app (B l E Y)).hom.app
          (op ((proEtaleBaseChange g).obj V)) b'))) •
      (show ((G₀ l E ϖ (h ≫ g) ac.coefficient).obj ((F₀ l E ϖ X).obj M)).val.obj
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V))) from
        ((G₀ l E ϖ (h ≫ g) ac.coefficient).obj ((F₀ l E ϖ X).obj M)).val.map
          ((MorphismProperty.Over.pullbackComp h g).inv.app V).op
          (unitSection l E ϖ (h ≫ g) ac.coefficient ((F₀ l E ϖ X).obj M) V
            (pbcTensorSection (iota l E ϖ X) M (op V) 1 m)))
  derived_square : ∀ K : PbcCompletedDerived X (pbcIntegralDatum l E),
    (F l E ϖ Z).map ((pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).inv.app K) ≫
      ac.derived.hom.app K =
    ah.derived.hom.app ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K) ≫
      (G l E ϖ h ah.coefficient).map (ag.derived.hom.app K) ≫
      derived.hom.app ((F l E ϖ X).obj K)

/-- Identity comparisons multiply the scalar into the module; their derived maps
are computed by exactly those chain maps on flat-term K-flat complexes. -/
structure Identity (X : Scheme.{u}) (a : Edge l E ϖ (𝟙 X)) where
  coefficient_id : a.coefficient = (proEtaleRingInverseImageId X).hom.app (R l E ϖ X)
  ordinary : G₀ l E ϖ (𝟙 X) a.coefficient ≅ 𝟭 _
  ordinary_tensor : ∀ (M : pbcModules X (R l E ϖ X)) (V : X.ProEt)
    (m : M.val.obj (op V))
    (e : (R l E ϖ X).obj.obj (op ((proEtaleBaseChange (𝟙 X)).obj V))),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 X)).obj V))
      (e • unitSection l E ϖ (𝟙 X) a.coefficient M V m) =
    e • M.val.map ((MorphismProperty.Over.pullbackId _ _ X).hom.app V).op m
  derived : G l E ϖ (𝟙 X) a.coefficient ≅ 𝟭 _
  derived_model : ∀ P : CochainComplex (pbcModules X (R l E ϖ X)) ℤ,
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      X.ProEt inferInstance (essentiallySmallSelf.{0} _)
      (ProEt.topology X) (R l E ϖ X) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology X) (R := R l E ϖ X) (P.X n)) →
    derived.hom.app (DerivedCategory.Q.obj P) = counit l E ϖ (𝟙 X) a.coefficient P ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex ordinary (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P)
  ordinary_square : ∀ M : pbcModules X (B l E X),
    a.ordinary.hom.app M ≫ ordinary.hom.app ((F₀ l E ϖ X).obj M) =
      (F₀ l E ϖ X).map ((pbcActualModulePullIdIso (pbcIntegralDatum l E) X).hom.app M)
  derived_square : ∀ K : PbcCompletedDerived X (pbcIntegralDatum l E),
    a.derived.hom.app K ≫ derived.hom.app ((F l E ϖ X).obj K) =
      (F l E ϖ X).map ((pbcActualDerivedPullIdIso (pbcIntegralDatum l E) X).hom.app K)

/-- Quotient transition, projection, identity and constant-scalar normalization.
Index n denotes the positive exponent n+1. -/
structure Coefficients : Prop where
  finite_comp : ∀ n : ℕ,
    completedFiniteCoefficientMap (h ≫ g) (pbcIntegralDatum l E) n =
      (proEtaleRingInverseImageComp h g).hom.app
          ((pbcAdicRings X (pbcIntegralDatum l E)).obj (op n)) ≫
        (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
          (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n) ≫
        completedFiniteCoefficientMap h (pbcIntegralDatum l E) n
  completed_comp : completedCoefficientMap (h ≫ g) (pbcIntegralDatum l E) =
    (proEtaleRingInverseImageComp h g).hom.app (B l E X) ≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (completedCoefficientMap g (pbcIntegralDatum l E)) ≫
      completedCoefficientMap h (pbcIntegralDatum l E)
  projection_comp : ∀ n : ℕ,
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (completedCoefficientMap g (pbcIntegralDatum l E)) ≫
      completedCoefficientMap h (pbcIntegralDatum l E) ≫
      pbcAdicProjection Z (pbcIntegralDatum l E) n =
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
          (pbcAdicProjection X (pbcIntegralDatum l E) n)) ≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n) ≫
      completedFiniteCoefficientMap h (pbcIntegralDatum l E) n
  finite_id : ∀ n : ℕ,
    completedFiniteCoefficientMap (𝟙 X) (pbcIntegralDatum l E) n =
      (proEtaleRingInverseImageId X).hom.app
        ((pbcAdicRings X (pbcIntegralDatum l E)).obj (op n))
  completed_id : completedCoefficientMap (𝟙 X) (pbcIntegralDatum l E) =
    (proEtaleRingInverseImageId X).hom.app (B l E X)
  transitions : ∀ {S T : Scheme.{u}} (f : S ⟶ T) {b a : ℕᵒᵖ} (q : b ⟶ a),
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        ((pbcAdicRings T (pbcIntegralDatum l E)).map q) ≫
      completedFiniteCoefficientMap f (pbcIntegralDatum l E) a.unop =
    completedFiniteCoefficientMap f (pbcIntegralDatum l E) b.unop ≫
      (pbcAdicRings S (pbcIntegralDatum l E)).map q
  scalar : ∀ {S T : Scheme.{u}} (f : S ⟶ T) (V : T.ProEt) (a : PbcIntegralRing l E),
    (completedCoefficientMap f (pbcIntegralDatum l E)).hom.app
      (op ((proEtaleBaseChange f).obj V))
      (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app (B l E T)).hom.app
        (op V) (pbcCompletedSection T (pbcIntegralDatum l E) (op V) a)) =
    pbcCompletedSection S (pbcIntegralDatum l E)
      (op ((proEtaleBaseChange f).obj V)) a

end AlgebraicGeometry.Scheme.LocalizedOrdinary
