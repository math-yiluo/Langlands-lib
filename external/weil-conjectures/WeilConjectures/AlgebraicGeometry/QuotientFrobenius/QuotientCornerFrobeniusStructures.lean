/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
public import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import WeilConjectures.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-! # Frobenius on quotient-coefficient corners and their strict completions

The quotient diagram is a ringed sequence site. All derived categories localize complexes
of strict systems, before evaluating. Restriction retains the completed coefficient action.

## Main definitions

- `QuotientFrobenius.WeilDatum`: the coherent strict quotient-diagram Weil input.
- `QuotientFrobenius.quotientCornerFrobeniusStructures`: all finite, strict and completed
  corner structures and their completed source and target reductions.
- `QuotientFrobenius.finite_formulas` and `QuotientFrobenius.towerTheta_evaluation`:
  the finite formulas and their compatibility with ambient scalar restriction.

## References

* Stacks 09A5
* Stacks 098T
* Stacks 03D3
* Stacks 03D8
* Stacks 06YY
* Stacks 03CZ
* Stacks 0D6E
* Stacks 0D6D
* Zheng 4.1
* Stacks 07A7
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.Scheme
namespace QuotientFrobenius

/-- The original small pro-etale site keeps its actual object and morphism universes. -/
instance (priority := 2000) baseSmall (T : Scheme.{t}) : EssentiallySmall.{t + 1} T.ProEt :=
  essentiallySmallSelf.{0} T.ProEt

attribute [local instance 2100] WeilConjectures.sfAbSheafify

attribute [local instance 2100] WeilConjectures.sfAbBijective

/-- Sheafification in the fixed coefficient universe of the quotient diagram site. -/
instance (priority := 2100) sequenceSheafify (T : Scheme.{t}) :
    HasSheafify (coefficientSequenceTopology (ProEt.topology T)) AddCommGrpCat.{t + 1} :=
  @SemilinearSections.abelianSheafify.{t + 1, t, t + 1} (ℕ × T.ProEt) _
    (essentiallySmallSelf.{0} _) _

/-- The coefficient-sized local bijectivity criterion on the quotient diagram site. -/
instance (priority := 2100) sequenceLocallyBijective (T : Scheme.{t}) :
    (coefficientSequenceTopology (ProEt.topology T)).WEqualsLocallyBijective
      AddCommGrpCat.{t + 1} :=
  @SemilinearSections.locallyBijective.{t + 1, t, t + 1} (ℕ × T.ProEt) _
    (essentiallySmallSelf.{0} _) _

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The actual finite quotient transitions, with index n representing exponent n+1. -/
abbrev transition (T : Scheme.{t}) (n : ℕ) :=
  (reductionCoefficientSystem T d).map (homOfLE (Nat.le_succ n)).op

/-- Q_T is the ring of finite quotient sheaves on the strict sequence site. -/
abbrev quotientRing (T : Scheme.{t}) :
    Sheaf (coefficientSequenceTopology (ProEt.topology T)) CommRingCat.{t + 1} :=
  @SemilinearSections.systemRing.{t + 1, t, t + 1} T.ProEt _
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T)
    (d.finiteRing T) (transition d T)

/-- Strict semilinear quotient systems; this is not a diagram category of derived objects. -/
abbrev modules (T : Scheme.{t}) : Type (t + 2) :=
  @SemilinearSections.Systems.{t + 1, t, t + 1} T.ProEt _
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T)
    (d.finiteRing T) (transition d T)

/-- The ordinary unbounded derived category on the ringed quotient diagram site. -/
abbrev derived (T : Scheme.{t}) : Type (t + 2) :=
  @SemilinearSections.DS.{t + 1, t, t + 1} T.ProEt _
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T)
    (d.finiteRing T) (transition d T)

/-- Exact quotient-linear evaluation, including the positive-level convention. -/
abbrev evaluation (T : Scheme.{t}) (n : ℕ) :=
  @SemilinearSections.e.{t + 1, t, t + 1} T.ProEt _
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T)
    (d.finiteRing T) (transition d T) n

/-- Base change on the vertical sequence sites, acting identically on the index. -/
abbrev siteMap {U V : Scheme.{t}} (u : U ⟶ V) :=
  (𝟭 ℕ).prod (proEtaleBaseChange u)

/-- Vertical covers are preserved by base change. -/
theorem siteMap_continuous {U V : Scheme.{t}} (u : U ⟶ V) :
    (siteMap u).IsContinuous (coefficientSequenceTopology (ProEt.topology V))
      (coefficientSequenceTopology (ProEt.topology U)) := by
  sorry

attribute [instance] siteMap_continuous

/-- The vertical slice of the strict ring is the specified finite coefficient sheaf. -/
theorem quotientRing_obj (T : Scheme.{t}) (W : (ℕ × T.ProEt)ᵒᵖ) :
    (quotientRing d T).obj.obj W = (d.finiteRing T W.unop.1).obj.obj (op W.unop.2) := by
  sorry

/-- Direct image and the quotient site have the same target section ring. -/
theorem coefficientTarget_obj {U V : Scheme.{t}} (u : U ⟶ V)
    (W : (ℕ × V.ProEt)ᵒᵖ) :
    (((proEtaleSheafDirectImage u CommRingCat.{t + 1}).obj
      (d.finiteRing U W.unop.1)).obj.obj (op W.unop.2)) =
      (quotientRing d U).obj.obj ((siteMap u).op.obj W) := by
  sorry

/-- Section component of the structural coefficient map, with explicit slice identifications. -/
def coefficientComponent {U V : Scheme.{t}} (u : U ⟶ V) (W : (ℕ × V.ProEt)ᵒᵖ) :
    (quotientRing d V).obj.obj W ⟶ (quotientRing d U).obj.obj ((siteMap u).op.obj W) :=
  eqToHom (quotientRing_obj d V W) ≫
    (proEtaleRingDirectImageMap u (d.finiteRing V W.unop.1)
      (d.finiteRing U W.unop.1) (d.finiteRingIso u W.unop.1)).hom.app (op W.unop.2) ≫
    eqToHom (coefficientTarget_obj d u W)

/-- Constant-section coefficient maps commute with horizontal quotient restrictions. -/
theorem coefficient_naturality {U V : Scheme.{t}} (u : U ⟶ V)
    {M N : (ℕ × V.ProEt)ᵒᵖ} (a : M ⟶ N) :
    (quotientRing d V).obj.map a ≫ coefficientComponent d u N =
      coefficientComponent d u M ≫ (quotientRing d U).obj.map ((siteMap u).op.map a) := by
  sorry

/-- The ring-system map uses the specified finite adjunct at every index and section. -/
def coefficientMap {U V : Scheme.{t}} (u : U ⟶ V) :
    SemilinearSections.ring.{t + 1, t, t + 1} _ (quotientRing d V) ⟶
      ((siteMap u).sheafPushforwardContinuous RingCat.{t + 1}
        (coefficientSequenceTopology (ProEt.topology V))
        (coefficientSequenceTopology (ProEt.topology U))).obj
          (SemilinearSections.ring.{t + 1, t, t + 1} _ (quotientRing d U)) where
  hom := Functor.whiskerRight
    ({ app := fun W ↦ coefficientComponent d u W
       naturality := fun _ _ a ↦ coefficient_naturality d u a } :
      (quotientRing d V).obj ⟶ (siteMap u).op ⋙ (quotientRing d U).obj)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})

/-- Sectionwise direct image on the quotient ringed sequence site. -/
abbrev modulePush {U V : Scheme.{t}} (u : U ⟶ V) : modules d U ⥤ modules d V :=
  SheafOfModules.pushforward.{t + 1} (F := siteMap u) (coefficientMap d u)

/-- Direct image is additive because it retains section maps and module addition. -/
theorem modulePush_additive {U V : Scheme.{t}} (u : U ⟶ V) :
    (modulePush d u).Additive := by
  sorry

attribute [instance] modulePush_additive

/-- The tensor-formula module pullback exists on the small quotient diagram sites. -/
theorem modulePush_isRightAdjoint {U V : Scheme.{t}} (u : U ⟶ V) :
    (modulePush d u).IsRightAdjoint := by
  sorry

attribute [instance] modulePush_isRightAdjoint

/-- Ordinary tensor pullback, fixed by the universal adjunction to actual direct image. -/
abbrev modulePull {U V : Scheme.{t}} (u : U ⟶ V) : modules d V ⥤ modules d U :=
  (modulePush d u).leftAdjoint

/-- The actual module adjunction, with the ordinary direct image fixed on sections. -/
def moduleAdjunction {U V : Scheme.{t}} (u : U ⟶ V) : modulePull d u ⊣ modulePush d u :=
  Adjunction.ofIsRightAdjoint (modulePush d u)

/-- Identified-coefficient inverse image is exact on the strict quotient diagram. -/
theorem modulePull_exact {U V : Scheme.{t}} (u : U ⟶ V) :
    (modulePull d u).Additive ∧ PreservesFiniteLimits (modulePull d u) ∧
      PreservesFiniteColimits (modulePull d u) := by
  sorry

/-- Additivity of quotient-diagram inverse image. -/
instance modulePull_additive {U V : Scheme.{t}} (u : U ⟶ V) :
    (modulePull d u).Additive := (modulePull_exact d u).1

/-- Left exactness of quotient-diagram inverse image. -/
instance modulePull_limits {U V : Scheme.{t}} (u : U ⟶ V) :
    PreservesFiniteLimits (modulePull d u) := (modulePull_exact d u).2.1

/-- Right exactness of quotient-diagram inverse image. -/
instance modulePull_colimits {U V : Scheme.{t}} (u : U ⟶ V) :
    PreservesFiniteColimits (modulePull d u) := (modulePull_exact d u).2.2

/-- K-injective resolutions in the actual quotient-system abelian category. -/
theorem modules_kinjective (T : Scheme.{t}) :
    Abelian.HasKInjectiveResolutions (modules d T) := by
  sorry

attribute [instance] modules_kinjective

/-- Total left derived pullback; exactness identifies it with termwise inverse image. -/
abbrev pull {U V : Scheme.{t}} (u : U ⟶ V) : derived d V ⥤ derived d U :=
  (modulePull d u).mapDerivedCategory

/-- K-injective total direct image on the category of strict quotient systems. -/
abbrev push {U V : Scheme.{t}} (u : U ⟶ V) : derived d U ⥤ derived d V :=
  (modulePush d u).rightDerivedFunctor

/-- The canonical module adjunction, derived before any evaluation. -/
def adjunction {U V : Scheme.{t}} (u : U ⟶ V) : pull d u ⊣ push d u :=
  (moduleAdjunction d u).mapDerivedCategoryRightDerivedAdjunction

/-- Direct-image composition is fixed by fibre-product pasting at every index and section. -/
theorem modulePushComp_exists {U V W : Scheme.{t}} (u : U ⟶ V) (v : V ⟶ W) :
    ∃! e : modulePush d u ⋙ modulePush d v ≅ modulePush d (u ≫ v),
      ∀ (N : modules d U) (n : ℕ) (Z : W.ProEt)
        (m : ((modulePush d u ⋙ modulePush d v).obj N).val.obj (op (n, Z))),
        HEq ((e.hom.app N).val.app (op (n, Z)) m)
          (N.val.map (Prod.mkHom (𝟙 n)
            ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) u v).hom.app
              Z)).op m) := by
  sorry

/-- Ordinary pullback composition is the conjugate of the specified sectionwise pasting. -/
def modulePullComp {U V W : Scheme.{t}} (u : U ⟶ V) (v : V ⟶ W) :
    modulePull d (u ≫ v) ≅ modulePull d v ⋙ modulePull d u :=
  (conjugateIsoEquiv
    ((moduleAdjunction d v).comp
      (moduleAdjunction d u))
    (moduleAdjunction d (u ≫ v))).symm
      (modulePushComp_exists d u v).exists.choose

/-- Derived composition is the localization of the ordinary tensor associator.
Since pullback is exact, this also gives its K-flat flat-term normalization. -/
def pullComp {U V W : Scheme.{t}} (u : U ⟶ V) (v : V ⟶ W) :
    pull d (u ≫ v) ≅ pull d v ⋙ pull d u :=
  Functor.mapDerivedCategoryNatIso (modulePullComp d u v) ≪≫
    (Functor.mapDerivedCategoryCompIso (modulePull d v) (modulePull d u)).symm

/-- The Frobenius face comparison, directed Phi_U Lu* to Lu* Phi_V. -/
def kappa {U V : Scheme.{t}} (u : U ⟶ V) (FU : U ≅ U) (FV : V ≅ V)
    (comm : FU.hom ≫ u = u ≫ FV.hom) :
    pull d u ⋙ pull d FU.hom ≅ pull d FV.hom ⋙ pull d u :=
  (pullComp d FU.hom u).symm ≪≫
    eqToIso (congrArg (fun a ↦ pull d a) comm) ≪≫ pullComp d u FV.hom

/-- Exchange along a Frobenius face is the adjunction mate of kappa inverse. -/
def beta {U V : Scheme.{t}} (u : U ⟶ V) (FU : U ≅ U) (FV : V ≅ V)
    (comm : FU.hom ≫ u = u ≫ FV.hom) :
    push d u ⋙ pull d FV.hom ⟶ pull d FU.hom ⋙ push d u :=
  mateEquiv (adjunction d u) (adjunction d u) (kappa d u FU FV comm).inv

/-- A constant coefficient presheaf is a sheaf on the vertical sequence site. -/
theorem diagonalRing_isSheaf (T : Scheme.{t}) :
    Presheaf.IsSheaf (coefficientSequenceTopology (ProEt.topology T))
      ((CategoryTheory.Prod.snd ℕ T.ProEt).op ⋙ (d.completedRing T).obj) := by
  sorry

/-- The completed-coefficient diagonal ring on the same vertical sequence site. -/
def diagonalRing (T : Scheme.{t}) :
    Sheaf (coefficientSequenceTopology (ProEt.topology T)) CommRingCat.{t + 1} :=
  ⟨(CategoryTheory.Prod.snd ℕ T.ProEt).op ⋙ (d.completedRing T).obj,
    diagonalRing_isSheaf d T⟩

/-- The projection component uses the fixed vertical-slice identification. -/
def diagonalProjectionComponent (T : Scheme.{t}) (W : (ℕ × T.ProEt)ᵒᵖ) :
    (diagonalRing d T).obj.obj W ⟶ (quotientRing d T).obj.obj W :=
  (d.projection T W.unop.1).hom.app (op W.unop.2) ≫
    eqToHom (quotientRing_obj d T W).symm

/-- The coefficient projections are natural on the strict diagram site. -/
theorem diagonalProjection_naturality (T : Scheme.{t})
    {M N : (ℕ × T.ProEt)ᵒᵖ} (a : M ⟶ N) :
    (diagonalRing d T).obj.map a ≫ diagonalProjectionComponent d T N =
      diagonalProjectionComponent d T M ≫ (quotientRing d T).obj.map a := by
  sorry

/-- The actual scalar map retaining all coefficient projections. -/
def diagonalProjection (T : Scheme.{t}) : diagonalRing d T ⟶ quotientRing d T where
  hom :=
    { app := fun W ↦ diagonalProjectionComponent d T W
      naturality := fun _ _ a ↦ diagonalProjection_naturality d T a }

/-- Projection to the original site is continuous for vertical covers. -/
theorem diagonal_continuous (T : Scheme.{t}) :
    (CategoryTheory.Prod.snd ℕ T.ProEt).IsContinuous
      (coefficientSequenceTopology (ProEt.topology T))
      (ProEt.topology T) := by
  sorry

attribute [instance] diagonal_continuous

/-- The exact diagonal module functor, implemented by its sectionwise pullback presheaf. -/
abbrev diagonal (T : Scheme.{t}) :
    proEtaleRingModules T (d.completedRing T) ⥤
      SemilinearSections.Mod.{t + 1, t, t + 1} (coefficientSequenceTopology (ProEt.topology T))
        (diagonalRing d T) :=
  SheafOfModules.pushforward.{t + 1} (F := CategoryTheory.Prod.snd ℕ T.ProEt) (𝟙 _)

/-- Diagonal retains addition of module maps on every section. -/
theorem diagonal_additive (T : Scheme.{t}) : (diagonal d T).Additive := by
  sorry

attribute [instance] diagonal_additive

/-- Diagonal is exact, since its restriction to every slice is identity. -/
theorem diagonal_exact (T : Scheme.{t}) :
    PreservesFiniteLimits (diagonal d T) ∧ PreservesFiniteColimits (diagonal d T) := by
  sorry

/-- Left exactness of diagonal. -/
instance diagonal_limits (T : Scheme.{t}) : PreservesFiniteLimits (diagonal d T) :=
  (diagonal_exact d T).1

/-- Right exactness of diagonal. -/
instance diagonal_colimits (T : Scheme.{t}) : PreservesFiniteColimits (diagonal d T) :=
  (diagonal_exact d T).2

/-- The universal K-flat scalar-extension pair for Delta A_T to Q_T. Its ordinary
functor is the sheafified tensor and its derived pair is fixed by the universal counit. -/
def scalarModel (T : Scheme.{t}) :=
  (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel.{t + 1, t, t + 1, t + 2, t + 2}
    (diagonalProjection d T)).some

/-- Additivity of the fixed ordinary scalar-extension functor in the universal pair. -/
instance scalarModel_additive (T : Scheme.{t}) : (scalarModel d T).E.Additive :=
  (scalarModel d T).additive

/-- The actual strict quotient reduction of K: diagonal followed by derived extension. -/
abbrev reduction (T : Scheme.{t}) : d.derived T ⥤ derived d T :=
  (diagonal d T).mapDerivedCategory ⋙ (scalarModel d T).T

/-- Restriction along Delta A_T to Q_T, followed by the normalized diagram realization. -/
theorem moduleRestriction_exists (T : Scheme.{t}) :
    ∃! R : modules d T ⥤ d.towers T,
      (∀ (M : modules d T) (n : ℕ),
        (R.obj M).obj (op n) = (reductionRestrict T (d.projection T n)).obj
          ((SemilinearSections.evaluation.{t + 1, t, t + 1}
            (ProEt.topology T) (d.finiteRing T) (transition d T) n).obj M)) ∧
      (∀ (M : modules d T) (m n : ℕ) (h : n ≤ m) (U : T.ProEtᵒᵖ),
        HEq (fun x ↦ (((R.obj M).map (homOfLE h).op).val.app U) x)
          (fun x : M.val.obj (op (m, U.unop)) ↦
            M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)) ∧
      (∀ {M N : modules d T} (a : M ⟶ N) (n : ℕ) (U : T.ProEtᵒᵖ),
        HEq (fun x ↦ (((R.map a).app (op n)).val.app U) x)
          (fun x : M.val.obj (op (n, U.unop)) ↦ a.val.app (op (n, U.unop)) x)) := by
  sorry

/-- The unique actual strict scalar restriction with the prescribed section maps. -/
def moduleRestriction (T : Scheme.{t}) : modules d T ⥤ d.towers T :=
  (moduleRestriction_exists d T).exists.choose

/-- Scalar restriction is additive and exact on the strict system category. -/
theorem moduleRestriction_exact (T : Scheme.{t}) :
    (moduleRestriction d T).Additive ∧ PreservesFiniteLimits (moduleRestriction d T) ∧
      PreservesFiniteColimits (moduleRestriction d T) := by
  sorry

/-- Additive scalar restriction. -/
instance moduleRestriction_additive (T : Scheme.{t}) : (moduleRestriction d T).Additive :=
  (moduleRestriction_exact d T).1

/-- Left exact scalar restriction. -/
instance moduleRestriction_limits (T : Scheme.{t}) :
    PreservesFiniteLimits (moduleRestriction d T) := (moduleRestriction_exact d T).2.1

/-- Right exact scalar restriction. -/
instance moduleRestriction_colimits (T : Scheme.{t}) :
    PreservesFiniteColimits (moduleRestriction d T) := (moduleRestriction_exact d T).2.2

/-- Derived strict scalar restriction, rather than forgetting to a family of objects. -/
abbrev restriction (T : Scheme.{t}) : derived d T ⥤ DerivedCategory (d.towers T) :=
  (moduleRestriction d T).mapDerivedCategory

/-- Ordinary restriction/direct-image comparison is identity on every section and index. -/
theorem moduleRestrictionPush_exists {U V : Scheme.{t}} (u : U ⟶ V) :
    ∃! e : modulePush d u ⋙ moduleRestriction d V ≅
        moduleRestriction d U ⋙ d.towerModulePush u,
      ∀ (M : modules d U) (n : ℕ) (Z : V.ProEtᵒᵖ),
        HEq (fun x ↦ (((e.hom.app M).app (op n)).val.app Z) x)
          (fun x : M.val.obj (op (n, (proEtaleBaseChange u).obj Z.unop)) ↦ x) := by
  sorry

/-- The section-normalized restriction/direct-image comparison before deriving. -/
def moduleRestrictionPush {U V : Scheme.{t}} (u : U ⟶ V) :=
  (moduleRestrictionPush_exists d u).exists.choose

/-- Restriction/pullback comparison fixed by the unit of the actual module adjunction. -/
theorem moduleRestrictionPull_exists {U V : Scheme.{t}} (u : U ⟶ V) :
    ∃! e : modulePull d u ⋙ moduleRestriction d U ≅
        moduleRestriction d V ⋙ d.towerModulePull u,
      ∀ M : modules d V,
        (moduleRestriction d V).map
            ((moduleAdjunction d u).unit.app M) ≫
          (moduleRestrictionPush d u).hom.app ((modulePull d u).obj M) ≫
          (d.towerModulePush u).map (e.hom.app M) =
            (d.towerModuleAdjunction u).unit.app ((moduleRestriction d V).obj M) := by
  sorry

/-- Exact descent of the normalized ordinary restriction/pullback isomorphism. -/
def restrictionPull {U V : Scheme.{t}} (u : U ⟶ V) :
    pull d u ⋙ restriction d U ≅ restriction d V ⋙ d.towerPull u :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (moduleRestrictionPull_exists d u).exists.choose ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Comparison of quotient and ambient derived direct image, normalized by universal units. -/
theorem restrictionPush_exists {U V : Scheme.{t}} (u : U ⟶ V) :
    ∃! e : push d u ⋙ restriction d V ≅ restriction d U ⋙ d.towerPush u,
      ∀ C : CochainComplex (modules d U) ℤ,
        (restriction d V).map
            ((DerivedCategory.quotientCompQhIso _).inv.app _ ≫
              (modulePush d u).rightDerivedFunctorUnit.app
                ((HomotopyCategory.quotient _ _).obj C) ≫
              (push d u).map ((DerivedCategory.quotientCompQhIso _).hom.app C)) ≫
          e.hom.app (DerivedCategory.Q.obj C) =
        (moduleRestriction d V).mapDerivedCategoryFactors.hom.app
            (((modulePush d u).mapHomologicalComplex (.up ℤ)).obj C) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (moduleRestrictionPush d u) (.up ℤ)).hom.app C) ≫
          exchangeTowerDerivedUnit u (d.completedRing V) (d.completedRing U)
            (d.integralRingIso u)
            (((moduleRestriction d U).mapHomologicalComplex (.up ℤ)).obj C) ≫
          (d.towerPush u).map ((moduleRestriction d U).mapDerivedCategoryFactors.inv.app C) := by
  sorry

/-- The canonical derived restriction/direct-image comparison with its unit normalization. -/
def restrictionPush {U V : Scheme.{t}} (u : U ⟶ V) :
    push d u ⋙ restriction d V ≅ restriction d U ⋙ d.towerPush u :=
  (restrictionPush_exists d u).exists.choose

/-- The representative counit of strict quotient reduction, retaining its tensor construction.
-/
def reductionCounit (T : Scheme.{t}) (P : CochainComplex (proEtaleRingModules T
    (d.completedRing T)) ℤ) :
    (reduction d T).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        ((((diagonal d T) ⋙ (scalarModel d T).E).mapHomologicalComplex (.up ℤ)).obj P) :=
  (scalarModel d T).T.map ((diagonal d T).mapDerivedCategoryFactors.hom.app P) ≫
    (scalarModel d T).ε.app (((diagonal d T).mapHomologicalComplex (.up ℤ)).obj P)

/-- Underived evaluation on the strict quotient module category. -/
abbrev moduleEvaluation (T : Scheme.{t}) (n : ℕ) :=
  @SemilinearSections.evaluation.{t + 1, t, t + 1} T.ProEt _
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T)
    (d.finiteRing T) (transition d T) n

/-- Evaluation/direct-image comparison fixed on all ordinary component carriers. -/
theorem moduleEvaluationPush_exists {U V : Scheme.{t}} (u : U ⟶ V) (n : ℕ) :
    ∃! e : modulePush d u ⋙ moduleEvaluation d V n ≅
        moduleEvaluation d U n ⋙ proEtaleRingModuleDirectImage u
          (d.finiteRing V n) (d.finiteRing U n) (d.finiteRingIso u n),
      ∀ (M : modules d U) (Z : V.ProEtᵒᵖ),
        HEq (fun x ↦ (e.hom.app M).val.app Z x)
          (fun x : M.val.obj (op (n, (proEtaleBaseChange u).obj Z.unop)) ↦ x) := by
  sorry

/-- The normalized ordinary evaluation of direct image. -/
def moduleEvaluationPush {U V : Scheme.{t}} (u : U ⟶ V) (n : ℕ) :=
  (moduleEvaluationPush_exists d u n).exists.choose

/-- Evaluation/pullback is fixed by the tensor-unit adjunction equation. -/
theorem moduleEvaluationPull_exists {U V : Scheme.{t}} (u : U ⟶ V) (n : ℕ) :
    ∃! e : modulePull d u ⋙ moduleEvaluation d U n ≅
        moduleEvaluation d V n ⋙ proEtaleRingModulePullback u
          (d.finiteRing V n) (d.finiteRing U n) (d.finiteRingIso u n),
      ∀ M : modules d V,
        (moduleEvaluation d V n).map
            ((moduleAdjunction d u).unit.app M) ≫
          (moduleEvaluationPush d u n).hom.app ((modulePull d u).obj M) ≫
          (proEtaleRingModuleDirectImage u (d.finiteRing V n) (d.finiteRing U n)
            (d.finiteRingIso u n)).map (e.hom.app M) =
          (proEtaleRingModuleAdjunction u (d.finiteRing V n) (d.finiteRing U n)
            (d.finiteRingIso u n)).unit.app ((moduleEvaluation d V n).obj M) := by
  sorry

/-- Exact descent of the unit-normalized evaluation/pullback comparison. -/
def evaluationPull {U V : Scheme.{t}} (u : U ⟶ V) (n : ℕ) :
    pull d u ⋙ evaluation d U n ≅ evaluation d V n ⋙ d.finitePull u n :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (moduleEvaluationPull_exists d u n).exists.choose ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The finite direct-image cochain unit, before any evaluation of a resolution. -/
def finitePushUnit {U V : Scheme.{t}} (u : U ⟶ V) (n : ℕ)
    (P : CochainComplex (proEtaleRingModules U (d.finiteRing U n)) ℤ) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      (((proEtaleRingModuleDirectImage u (d.finiteRing V n) (d.finiteRing U n)
        (d.finiteRingIso u n)).mapHomologicalComplex (.up ℤ)).obj P) ≫
    (proEtaleRingModuleDirectImage u (d.finiteRing V n) (d.finiteRing U n)
      (d.finiteRingIso u n)).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj P) ≫
    (d.finitePush u n).map ((DerivedCategory.quotientCompQhIso _).hom.app P)

/-- Ordinary ambient tower evaluation at the paper's positive level n+1. -/
abbrev ambientModuleEvaluation (T : Scheme.{t}) (n : ℕ) :=
  reductionTowerEvaluation T (reductionModuleRing T (d.completedRing T)) n

/-- Derived ambient evaluation, using exact termwise evaluation. -/
abbrev ambientEvaluation (T : Scheme.{t}) (n : ℕ) :=
  reductionTowerDerivedEvaluation T (reductionModuleRing T (d.completedRing T)) n

/-- Exact restriction of the finite coefficient action to the completed coefficient action. -/
abbrev finiteRestriction (T : Scheme.{t}) (n : ℕ) :=
  reductionDerivedRestrict T (d.projection T n)

/-- Restriction and evaluation commute by the identity on the original section carriers. -/
theorem moduleRestrictionEvaluation_exists (T : Scheme.{t}) (n : ℕ) :
    ∃! e : moduleRestriction d T ⋙ ambientModuleEvaluation d T n ≅
        moduleEvaluation d T n ⋙ reductionRestrict T (d.projection T n),
      ∀ (M : modules d T) (U : T.ProEtᵒᵖ),
        HEq (fun x ↦ (e.hom.app M).val.app U x)
          (fun x : M.val.obj (op (n, U.unop)) ↦ x) := by
  sorry

/-- Derived restriction/evaluation, induced by the ordinary identity of section carriers. -/
def restrictionEvaluation (T : Scheme.{t}) (n : ℕ) :
    restriction d T ⋙ ambientEvaluation d T n ≅
      evaluation d T n ⋙ finiteRestriction d T n :=
  Functor.mapDerivedCategoryCompIso (moduleRestriction d T)
    (ambientModuleEvaluation d T n) ≪≫
    Functor.mapDerivedCategoryNatIso
      (moduleRestrictionEvaluation_exists d T n).exists.choose ≪≫
    (Functor.mapDerivedCategoryCompIso (moduleEvaluation d T n)
      (reductionRestrict T (d.projection T n))).symm

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Automorphisms of the four schemes of a Cartesian square commuting with all four edges,
forming a cube. -/
structure Cube (_sq : ChosenCartesianSquare g' f' f g) where
  FX : X ≅ X
  FY : Y ≅ Y
  FX' : X' ≅ X'
  FY' : Y' ≅ Y'
  f_comm : FX.hom ≫ f = f ≫ FY.hom
  g_comm : FY'.hom ≫ g = g ≫ FY.hom
  g'_comm : FX'.hom ≫ g' = g' ≫ FX.hom
  f'_comm : FX'.hom ≫ f' = f' ≫ FY'.hom

/-- Each commutative face with invertible horizontal edges is Cartesian. -/
theorem face_isPullback {U V : Scheme.{t}} (u : U ⟶ V) (FU : U ≅ U) (FV : V ≅ V)
    (comm : FU.hom ≫ u = u ≫ FV.hom) : IsPullback FU.hom u u FV.hom := by
  sorry

/-- The chosen Cartesian identification is the universal one for the Frobenius face. -/
def face {U V : Scheme.{t}} (u : U ⟶ V) (FU : U ≅ U) (FV : V ≅ V)
    (comm : FU.hom ≫ u = u ≫ FV.hom) :
    ChosenCartesianSquare FU.hom u u FV.hom where
  w := comm
  isoPullback := (face_isPullback u FU FV comm).isoPullback
  hom_fst := (face_isPullback u FU FV comm).isoPullback_hom_fst
  hom_snd := (face_isPullback u FU FV comm).isoPullback_hom_snd

/-- Integral beta is exactly the canonical ambient ringed exchange of the Frobenius face. -/
abbrev integralBeta {U V : Scheme.{t}} (u : U ⟶ V) (FU : U ≅ U) (FV : V ≅ V)
    (comm : FU.hom ≫ u = u ≫ FV.hom) :=
  d.integralExchange (face u FU FV comm)

/-- A coherent Weil structure is an isomorphism on the derived strict quotient diagram.
Its existence is data; no equality of evaluated morphisms is used as a substitute. -/
structure WeilDatum (sq : ChosenCartesianSquare g' f' f g) (K : d.derived X)
    extends Cube sq where
  theta : (pull d FX.hom).obj ((reduction d X).obj K) ≅ (reduction d X).obj K

variable {sq : ChosenCartesianSquare g' f' f g} {K : d.derived X}
  (F : WeilDatum d sq K)

/-- The quotient diagram's B and D corners, constructed by its actual total operations. -/
abbrev cornerB := (pull d g).obj ((push d f).obj ((reduction d X).obj K))

/-- The quotient diagram's D corner, with ordinary uncompleted pullback on X'. -/
abbrev cornerD := (push d f').obj ((pull d g').obj ((reduction d X).obj K))

/-- Theta_E is pullback of the strict Weil map after the specified pullback composition. -/
def thetaE :
    (pull d F.FX'.hom).obj ((pull d g').obj ((reduction d X).obj K)) ⟶
      (pull d g').obj ((reduction d X).obj K) :=
  (kappa d g' F.FX' F.FX F.g'_comm).hom.app ((reduction d X).obj K) ≫
    (pull d g').map F.theta.hom

/-- Theta_B is kappa_g, followed by Lg* beta_f, followed by Lg* Rf* theta. -/
def thetaB : (pull d F.FY'.hom).obj (cornerB (f := f) (g := g) d (K := K)) ⟶
    cornerB (f := f) (g := g) d (K := K) :=
  (kappa d g F.FY' F.FY F.g_comm).hom.app ((push d f).obj ((reduction d X).obj K)) ≫
    (pull d g).map ((beta d f F.FX F.FY F.f_comm).app ((reduction d X).obj K)) ≫
    (pull d g).map ((push d f).map F.theta.hom)

/-- Theta_D is beta_f' followed by Rf'* theta_E, on the strict quotient diagram itself. -/
def thetaD : (pull d F.FY'.hom).obj (cornerD (f' := f') (g' := g') d (K := K)) ⟶
    cornerD (f' := f') (g' := g') d (K := K) :=
  (beta d f' F.FX' F.FY' F.f'_comm).app ((pull d g').obj ((reduction d X).obj K)) ≫
    (push d f').map (thetaE d F)

/-- Finite-linear evaluation of a strict Frobenius structure through its fixed comparison. -/
def finiteTransport {T : Scheme.{t}} (FT : T ≅ T) (n : ℕ) {M : derived d T}
    {N : DerivedCategory (proEtaleRingModules T (d.finiteRing T n))}
    (c : (evaluation d T n).obj M ≅ N) (theta : (pull d FT.hom).obj M ⟶ M) :
    (d.finitePull FT.hom n).obj N ⟶ N :=
  (d.finitePull FT.hom n).map c.inv ≫
    (evaluationPull d FT.hom n).inv.app M ≫ (evaluation d T n).map theta ≫ c.hom

/-- Transport a quotient-diagram Frobenius map by restriction and the specified comparison. -/
def transport {T : Scheme.{t}} (FT : T ≅ T) {M : derived d T}
    {N : DerivedCategory (d.towers T)}
    (c : (restriction d T).obj M ≅ N) (theta : (pull d FT.hom).obj M ⟶ M) :
    (d.towerPull FT.hom).obj N ⟶ N :=
  (d.towerPull FT.hom).map c.inv ≫
    (restrictionPull d FT.hom).inv.app M ≫ (restriction d T).map theta ≫ c.hom

end QuotientFrobenius
end AlgebraicGeometry.Scheme
