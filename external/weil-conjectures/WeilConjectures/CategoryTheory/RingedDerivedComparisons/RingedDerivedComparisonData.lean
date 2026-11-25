/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorSquarePresentation
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
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
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
/-! # Data for normalized derived monoidal comparisons on ringed topoi

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 0D6D, 07A6, 0D6E, 0FPI;
Modules on Sites, Tags 03D7, 03D8, 03EL
(blueprint: def-sfb-ringed-derived-comparison-data).

The structures below only package the simultaneous witnesses of the statement. In
particular an ordinary pullback is tied to the geometric morphism by scalar extension
and its underlying Hom bijection. Derived adjunctions are fixed on K-flat/K-injective
representatives. The comparisons are fixed on representatives, including for a specified
geometric 2-isomorphism; none is an unconstrained isomorphism of functors.
-/

@[expose] public noncomputable section

set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits WeilConjectures SheafOfModules

namespace CategoryTheory.RingedDerivedComparisons

set_option linter.checkUnivs false in
/-- A presentation of the ordinary derived category with its recorded signed tensor model.
Source: Stacks 0FPT, 06YN (blueprint: def-sfb-ringed-derived-comparison-data).
These are the witnesses of `ringedDerived_closed_symmetric_monoidal`, not new tensor data. -/
structure Site where
  C : Type u
  [category : SmallCategory C]
  J : GrothendieckTopology C
  A : Sheaf J CommRingCat.{u}
  [derived : HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A))]
  closed : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, u, u, w} J A)
  model : CoefficientTensorModels.{u, u, u, w} J A closed
  symmetry : @SymmetricCategory _ _ closed.monoidal
  coherence : RingedDerivedTensorCoherence.{u, u, u, w} J A closed model symmetry

attribute [instance] Site.category Site.derived

/-- The recorded ring sheaf, with commutativity forgotten.
Source: Stacks 03D7 (blueprint: def-sfb-ringed-derived-comparison-data). -/
abbrev Site.ring (X : Site.{u, w}) :=
  (sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.A

/-- The existing module category of a corner.
Source: Stacks 03D7 (blueprint: def-sfb-ringed-derived-comparison-data). -/
abbrev Site.modules (X : Site.{u, w}) := ringedSiteModules.{u, u, u, u} X.ring

/-- The ordinary unbounded derived category of that module category.
Source: Stacks 05RR (blueprint: def-sfb-ringed-derived-comparison-data). -/
abbrev Site.D (X : Site.{u, w}) := DerivedCategory.{w} X.modules

/-- The underlying sheaf functor used to specify ordinary scalar-extension insertion.
Source: Stacks 03D7 (blueprint: def-sfb-ringed-derived-comparison-data). -/
abbrev Site.sets (X : Site.{u, w}) :=
  toSheaf X.ring ⋙ sheafCompose X.J (CategoryTheory.forget AddCommGrpCat.{u})

/-- The tensor corner of the existing projection-mate interface, with this very tensor.
Source: Stacks 07A4 (blueprint: def-sfb-ringed-derived-comparison-data). -/
def Site.corner (X : Site.{u, w}) : RingedTensorCorner.{u, w} where
  site := X.C
  topology := X.J
  ring := X.A
  tensor := X.closed.tensor

/-- Morphisms are exactly the DAG's geometric ringed-topos morphisms.
Source: Stacks 03D7 (blueprint: def-sfb-ringed-derived-comparison-data). -/
abbrev Morphism (X Y : Site.{u, w}) := RingedToposMorphism X.ring Y.ring

/-- All normalization data for one of the statement's pullback/direct-image pairs.
Source: Stacks 07A4, 07A6, 0FPI, 03D7
(blueprint: def-sfb-ringed-derived-comparison-data).
The `CoreMonoidal` maps are inverse to the displayed tensor/unit comparisons. -/
structure Lift {X Y : Site.{u, w}} (f : Morphism X Y) where
  edge : RingedTensorEdge Y.corner X.corner
  inverse_eq : edge.inverse = f.inverse
  direct_eq : edge.direct = f.direct
  geometric_adjunction : HEq edge.adjunction f.adj
  pushforward_eq : edge.pushforward = f.modules
  structural_map :
    edge.algebraic.ringUnderlying.hom ≫
        (sheafCompose X.J (CategoryTheory.forget CommRingCat.{u})).map edge.ringMap =
      eqToHom (congrArg (fun F ↦ F.obj
        ((sheafCompose Y.J (CategoryTheory.forget CommRingCat.{u})).obj Y.A)) inverse_eq) ≫
          f.ringMap
  ordinary_adjunction : ∀ (M : Y.modules) (N : X.modules) (v : edge.pullback.obj M ⟶ N),
    Y.sets.map (edge.moduleAdjunction.homEquiv M N v) ≫
      (Functor.whiskerRight (eqToHom pushforward_eq) Y.sets).app N ≫
        f.underlying.hom.app N =
      f.adj.homEquiv (Y.sets.obj M) (X.sets.obj N)
        (eqToHom (congrArg (fun F ↦ F.obj (Y.sets.obj M)) inverse_eq.symm) ≫
          edge.insertion M ≫ X.sets.map v)
  [right_additive : edge.pushforward.Additive]
  eta : edge.pushforward.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q.{w} (C := Y.modules) ⟶
    DerivedCategory.Q.{w} (C := X.modules) ⋙ edge.right
  isRightDerived : edge.right.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso X.modules (ComplexShape.up ℤ))
  eta_injective : ∀ I : CochainComplex X.modules ℤ, I.IsKInjective → IsIso (eta.app I)
  epsilon_flat : ∀ P : CochainComplex Y.modules ℤ,
    Y.corner.mateFlat P → IsIso (derivedPullbackComplexComparison
      edge.pullback edge.left edge.epsilon P)
  canonical_adjunction : ∀ (P : CochainComplex Y.modules ℤ)
    (I : CochainComplex X.modules ℤ), Y.corner.mateFlat P → I.IsKInjective →
    ∀ b : P ⟶ (edge.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I,
      (edge.derivedAdjunction.homEquiv (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj I)).symm (DerivedCategory.Q.map b ≫ eta.app I) =
      derivedPullbackComplexComparison edge.pullback edge.left edge.epsilon P ≫
        DerivedCategory.Q.map
          (((edge.moduleAdjunction.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv P I).symm b)
  tensorModelY : RingedTensorModel Y.corner
  tensorModelX : RingedTensorModel X.corner
  tensorModelY_eq : ∀ P Q hP hQ,
    tensorModelY.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
      (Y.model.iso Y.J Y.A Y.closed P Q hP.1 hQ.1).hom
  tensorModelX_eq : ∀ P Q hP hQ,
    tensorModelX.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
      (X.model.iso X.J X.A X.closed P Q hP.1 hQ.1).hom
  monoidal : @Functor.CoreMonoidal Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal edge.left
  tensor_canonical : ∀ U V : Y.D,
    (@Functor.CoreMonoidal.μIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
      edge.left monoidal U V).inv =
      (edge.tensorComparison tensorModelY tensorModelX).hom.app (U, V)
  unit_canonical : ∃ j : edge.pullback.obj (SheafOfModules.unit Y.ring) ≅
      SheafOfModules.unit X.ring,
    (∀ M : Y.modules,
      (edge.ordinaryTensor.mu M (SheafOfModules.unit Y.ring)).hom ≫
          (SheafOfModules.monoidalCategory X.A).tensorHom (𝟙 _) j.hom ≫
          ((SheafOfModules.monoidalCategory X.A).rightUnitor (edge.pullback.obj M)).hom =
        edge.pullback.map ((SheafOfModules.monoidalCategory Y.A).rightUnitor M).hom) ∧
    edge.left.map Y.coherence.unitIso.hom ≫
        derivedPullbackComplexComparison edge.pullback edge.left edge.epsilon
          (ringedTensorUnitComplex.{u, u, u} Y.J Y.A) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
            edge.pullback (ComplexShape.up ℤ) 0).hom.app (SheafOfModules.unit Y.ring) ≫
            (CochainComplex.singleFunctor X.modules 0).map j.hom) ≫
        X.coherence.unitIso.inv =
        (@Functor.CoreMonoidal.εIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
          edge.left monoidal).inv
  symmetric : ∀ U V : Y.D,
    (@Functor.CoreMonoidal.μIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
      edge.left monoidal U V).inv ≫
        (X.symmetry.toBraidedCategory.braiding (edge.left.obj U) (edge.left.obj V)).hom =
      edge.left.map (Y.symmetry.toBraidedCategory.braiding U V).hom ≫
        (@Functor.CoreMonoidal.μIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
          edge.left monoidal V U).inv

attribute [instance] Lift.right_additive

attribute [local irreducible] SheafOfModules.monoidalCategory

/-- Scalar-extension insertion referred to the given geometric inverse image.
Source: Stacks 03D7, 03EL (blueprint: def-sfb-ringed-derived-comparison-data). -/
def Lift.insertion {X Y : Site.{u, w}} {f : Morphism X Y} (l : Lift f) (M : Y.modules) :
    f.inverse.obj (Y.sets.obj M) ⟶ X.sets.obj (l.edge.pullback.obj M) :=
  eqToHom (congrArg (fun F ↦ F.obj (Y.sets.obj M)) l.inverse_eq.symm) ≫ l.edge.insertion M

/-- The canonical K-flat representative map, without a new choice of isomorphism.
Source: Stacks 06YY, 0FPI (blueprint: def-sfb-ringed-derived-comparison-data). -/
abbrev Lift.alpha {X Y : Site.{u, w}} {f : Morphism X Y} (l : Lift f)
    (P : CochainComplex Y.modules ℤ) :=
  derivedPullbackComplexComparison l.edge.pullback l.edge.left l.edge.epsilon P

/-- The inverse tensorator, equal to the uniquely characterized canonical tensor comparison.
Source: Stacks 07A4 (blueprint: def-sfb-ringed-derived-comparison-data). -/
abbrev Lift.tensor {X Y : Site.{u, w}} {f : Morphism X Y} (l : Lift f) (U V : Y.D) :=
  (@Functor.CoreMonoidal.μIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
    l.edge.left l.monoidal U V).symm

/-- The inverse unit comparison; its degree-zero normalization is `unit_canonical`.
Source: Stacks 07A4, 03EL (blueprint: def-sfb-ringed-derived-comparison-data). -/
abbrev Lift.unit {X Y : Site.{u, w}} {f : Morphism X Y} (l : Lift f) :=
  (@Functor.CoreMonoidal.εIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
    l.edge.left l.monoidal).symm

/-- Normalization for a composite represented by the specified geometric path isomorphism.
The ordinary comparison is fixed by insertion, and kappa by its right-derived units.
Source: Stacks 0D6D, 0D6E, 07A6, 03D8
(blueprint: def-sfb-ringed-derived-comparison-data). -/
structure Composition {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    (lf : Lift f) (lg : Lift g) (lk : Lift k)
    (θ : k.inverse ≅ g.inverse ⋙ f.inverse) where
  ordinary : lk.edge.pullback ≅ lg.edge.pullback ⋙ lf.edge.pullback
  ordinary_insertion : ∀ M : Z.modules,
    lk.insertion M ≫ X.sets.map (ordinary.hom.app M) =
      θ.hom.app (Z.sets.obj M) ≫ f.inverse.map (lg.insertion M) ≫
        lf.insertion (lg.edge.pullback.obj M)
  ordinary_right : lk.edge.pushforward ≅ lf.edge.pushforward ⋙ lg.edge.pushforward
  ordinary_mate : ordinary_right =
    conjugateIsoEquiv lk.edge.moduleAdjunction
      (lg.edge.moduleAdjunction.comp lf.edge.moduleAdjunction) ordinary.symm
  pullback : lk.edge.left ≅ lg.edge.left ⋙ lf.edge.left
  pullback_model : ∀ (P : CochainComplex Z.modules ℤ), Z.corner.mateFlat P →
    pullback.hom.app (DerivedCategory.Q.obj P) ≫
      lf.edge.left.map (lg.alpha P) ≫
      lf.alpha ((lg.edge.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
    lk.alpha P ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex ordinary.hom (ComplexShape.up ℤ)).app P)
  kappa : lk.edge.right ≅ lf.edge.right ⋙ lg.edge.right
  kappa_model : ∀ I : CochainComplex X.modules ℤ,
    lk.eta.app I ≫ kappa.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ordinary_right.hom (ComplexShape.up ℤ)).app I) ≫
        lg.eta.app ((lf.edge.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
          lg.edge.right.map (lf.eta.app I)
  tensor : ∀ U V : Z.D,
    pullback.hom.app (Z.closed.tensor.obj (U, V)) ≫
      lf.edge.left.map (lg.tensor U V).hom ≫
      (lf.tensor (lg.edge.left.obj U) (lg.edge.left.obj V)).hom =
    (lk.tensor U V).hom ≫
      X.closed.tensor.map
        (X := (lk.edge.left.obj U, lk.edge.left.obj V))
        (Y := (lf.edge.left.obj (lg.edge.left.obj U), lf.edge.left.obj (lg.edge.left.obj V)))
        (pullback.hom.app U, pullback.hom.app V)
  unit : pullback.hom.app Z.closed.monoidal.tensorUnit ≫
      lf.edge.left.map lg.unit.hom ≫ lf.unit.hom = lk.unit.hom
  homEquiv : ∀ (U : Z.D) (E : X.D) (b : lk.edge.left.obj U ⟶ E),
    lk.edge.derivedAdjunction.homEquiv U E b ≫ kappa.hom.app E =
      (lg.edge.derivedAdjunction.comp lf.edge.derivedAdjunction).homEquiv U E
        (pullback.inv.app U ≫ b)
  counit : ∀ E : X.D,
    lk.edge.left.map (kappa.hom.app E) ≫
      pullback.hom.app ((lf.edge.right ⋙ lg.edge.right).obj E) ≫
      lf.edge.left.map (lg.edge.derivedAdjunction.counit.app (lf.edge.right.obj E)) ≫
      lf.edge.derivedAdjunction.counit.app E = lk.edge.derivedAdjunction.counit.app E

/-- Identity normalization, including the specified tensor and the entire adjunction.
Source: Stacks 07A4, 07A6, 03D7
(blueprint: def-sfb-ringed-derived-comparison-data). -/
structure Identity {X : Site.{u, w}} {f : Morphism X X} (l : Lift f)
    (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u))) where
  ordinary : l.edge.pullback ≅ 𝟭 X.modules
  ordinary_insertion : ∀ M : X.modules,
    l.insertion M ≫ X.sets.map (ordinary.hom.app M) = θ.hom.app (X.sets.obj M)
  ordinary_right : l.edge.pushforward ≅ 𝟭 X.modules
  ordinary_mate : ordinary_right =
    conjugateIsoEquiv l.edge.moduleAdjunction (Adjunction.id (C := X.modules)) ordinary.symm
  pullback : l.edge.left ≅ 𝟭 X.D
  pullback_model : ∀ P : CochainComplex X.modules ℤ, X.corner.mateFlat P →
    ∃ a : (l.edge.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ P,
      (∀ n : ℤ, a.f n = ordinary.hom.app (P.X n)) ∧
      pullback.hom.app (DerivedCategory.Q.obj P) = l.alpha P ≫ DerivedCategory.Q.map a
  pushforward : l.edge.right ≅ 𝟭 X.D
  pushforward_model : ∀ I : CochainComplex X.modules ℤ,
    ∃ a : (l.edge.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ I,
      (∀ n : ℤ, a.f n = ordinary_right.hom.app (I.X n)) ∧
      l.eta.app I ≫ pushforward.hom.app (DerivedCategory.Q.obj I) = DerivedCategory.Q.map a
  tensor : ∀ U V : X.D,
    (l.tensor U V).hom ≫ X.closed.tensor.map
        (X := (l.edge.left.obj U, l.edge.left.obj V)) (Y := (U, V))
        (pullback.hom.app U, pullback.hom.app V) =
      pullback.hom.app (X.closed.tensor.obj (U, V))
  unit : l.unit.hom = pullback.hom.app X.closed.monoidal.tensorUnit
  homEquiv : ∀ (U E : X.D) (b : l.edge.left.obj U ⟶ E),
    l.edge.derivedAdjunction.homEquiv U E b ≫ pushforward.hom.app E =
      (Adjunction.id (C := X.D)).homEquiv U E (pullback.inv.app U ≫ b)

/-- Transport along the given, ring-compatible geometric 2-isomorphism.
The insertion equation fixes its value on every generalized scalar-extension generator.
Source: Stacks 03D7, 03EL, 07A4, 07A6
(blueprint: def-sfb-ringed-derived-comparison-data). -/
structure TwoIso {X Y : Site.{u, w}} {h k : Morphism X Y}
    (lh : Lift h) (lk : Lift k) (θ : h.inverse ≅ k.inverse) where
  ordinary : lh.edge.pullback ≅ lk.edge.pullback
  ordinary_insertion : ∀ M : Y.modules,
    lh.insertion M ≫ X.sets.map (ordinary.hom.app M) =
      θ.hom.app (Y.sets.obj M) ≫ lk.insertion M
  ordinary_right : lk.edge.pushforward ≅ lh.edge.pushforward
  ordinary_mate : ordinary_right =
    conjugateIsoEquiv lk.edge.moduleAdjunction lh.edge.moduleAdjunction ordinary
  pullback : lh.edge.left ≅ lk.edge.left
  pullback_model : ∀ P : CochainComplex Y.modules ℤ, Y.corner.mateFlat P →
    pullback.hom.app (DerivedCategory.Q.obj P) ≫ lk.alpha P =
      lh.alpha P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ordinary.hom (ComplexShape.up ℤ)).app P)
  pushforward : lk.edge.right ≅ lh.edge.right
  pushforward_model : ∀ I : CochainComplex X.modules ℤ,
    lk.eta.app I ≫ pushforward.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ordinary_right.hom (ComplexShape.up ℤ)).app I) ≫
        lh.eta.app I
  tensor : ∀ U V : Y.D,
    pullback.hom.app (Y.closed.tensor.obj (U, V)) ≫ (lk.tensor U V).hom =
      (lh.tensor U V).hom ≫ X.closed.tensor.map
        (X := (lh.edge.left.obj U, lh.edge.left.obj V))
        (Y := (lk.edge.left.obj U, lk.edge.left.obj V))
        (pullback.hom.app U, pullback.hom.app V)
  unit : pullback.hom.app Y.closed.monoidal.tensorUnit ≫ lk.unit.hom = lh.unit.hom
  homEquiv : ∀ (U : Y.D) (E : X.D) (b : lk.edge.left.obj U ⟶ E),
    lh.edge.derivedAdjunction.homEquiv U E (pullback.hom.app U ≫ b) =
      lk.edge.derivedAdjunction.homEquiv U E b ≫ pushforward.hom.app E

set_option linter.checkUnivs false in
/-- All clauses of the normalization statement, universally over the presented sites.
Source: Stacks 07A4, 0D6D, 07A6, 0D6E, 0FPI
(blueprint: def-sfb-ringed-derived-comparison-data).
The auxiliary morphism k is the composite represented by theta; allowing any such
presentation also retains arbitrary ring-compatible path isomorphisms. -/
structure System where
  lift : ∀ {X Y : Site.{u, w}}, (f : Morphism X Y) → Lift f
  composites : ∀ {X Y Z : Site.{u, w}} (f : Morphism X Y) (g : Morphism Y Z),
    ∃ (k : Morphism X Z) (θ : k.inverse ≅ g.inverse ⋙ f.inverse),
      k.ringMap = θ.hom.app ((sheafCompose Z.J
        (CategoryTheory.forget CommRingCat.{u})).obj Z.A) ≫
          f.inverse.map g.ringMap ≫ f.ringMap
  identities : ∀ X : Site.{u, w},
    ∃ (f : Morphism X X) (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u))),
      f.ringMap = θ.hom.app ((sheafCompose X.J
        (CategoryTheory.forget CommRingCat.{u})).obj X.A)
  composition : ∀ {X Y Z : Site.{u, w}} (f : Morphism X Y) (g : Morphism Y Z)
    (k : Morphism X Z) (θ : k.inverse ≅ g.inverse ⋙ f.inverse),
    k.ringMap = θ.hom.app ((sheafCompose Z.J
      (CategoryTheory.forget CommRingCat.{u})).obj Z.A) ≫
        f.inverse.map g.ringMap ≫ f.ringMap →
    Nonempty (Composition (lift f) (lift g) (lift k) θ)
  identity : ∀ (X : Site.{u, w}) (f : Morphism X X)
    (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u))),
    f.ringMap = θ.hom.app ((sheafCompose X.J
      (CategoryTheory.forget CommRingCat.{u})).obj X.A) → Nonempty (Identity (lift f) θ)
  twoIso : ∀ {X Y : Site.{u, w}} (h k : Morphism X Y) (θ : h.inverse ≅ k.inverse),
    h.ringMap = θ.hom.app ((sheafCompose Y.J
      (CategoryTheory.forget CommRingCat.{u})).obj Y.A) ≫ k.ringMap →
    Nonempty (TwoIso (lift h) (lift k) θ)

end CategoryTheory.RingedDerivedComparisons
