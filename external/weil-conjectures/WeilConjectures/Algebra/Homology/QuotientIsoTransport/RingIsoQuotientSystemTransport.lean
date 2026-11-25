/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemDerivedTransitionCoherence
public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import WeilConjectures.Algebra.Homology.System.SystemDerivedTransitionUnit
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Limits.Final
import all WeilConjectures.CategoryTheory.Constant.ConstantTowerNormalization
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.Derived.DerivedMateComparison
import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation

/-! # Coherent transport of strict quotient systems

Source: lemma-section-normal-bundle--1, finite-clopen expansion, steps 2--3 and 5;
Stacks 03D7, 03EK, 015F, 06YY and 07A6
(blueprint: lem-pur-ring-iso-quotient-system-transport).

The structures below spell out the normalization of the equivalence, its scalar
comparisons and its whole-system derived reduction. They are interfaces for this
single theorem. All module categories, restrictions, tensors, adjunctions and
localizations are the recorded library constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance 11000] hasSheafCompose_of_preservesLimitsOfSize
attribute [local instance 11000] SheafOfModules.instPreadditive
attribute [local instance 11000] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance 20000] SheafOfModules.systemEvaluationAdditive
  SheafOfModules.systemEvaluationLimits SheafOfModules.systemEvaluationColimits

attribute [local instance 12000] SheafOfModules.systemRingHasDerived
attribute [local instance 12000] SheafOfModules.strictRingSystemHasDerived
attribute [local instance 12000] SheafOfModules.strictRingSystemAbelian
attribute [local instance 12000] SheafOfModules.instAbelian

namespace SheafOfModules.QuotientIsoTransport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- Use the specified sheafification adjunction directly.
Source: Stacks 03DA (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
theorem moduleWeakSheafify : HasWeakSheafify J AddCommGrpCat.{w} :=
  HasSheafify.isRightAdjoint

attribute [local instance 20000] moduleWeakSheafify

/-- Module sheaves in the coefficient universe, using the recorded category.
Source: Stacks 03DA (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
abbrev Modules (R : Sheaf J CommRingCat.{w}) :=
  ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)

/-- Scalar transport is literally restriction along the inverse ring isomorphism.
Source: Stacks 03CZ (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def transport {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) : Modules R ⥤ Modules S :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map a.inv)

/-- Additivity for inverse scalar restriction.
Source: Stacks 03D7 (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
instance transportAdditive {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    (transport a).Additive := by
  unfold transport
  infer_instance

/-- Preservation of finite limits for inverse scalar restriction.
Source: Stacks 03D7 (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
instance transportLimits {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    PreservesFiniteLimits (transport a) := by
  unfold transport
  infer_instance

/-- Preservation of finite colimits for inverse scalar restriction.
Source: Stacks 03D7 (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
instance transportColimits {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    PreservesFiniteColimits (transport a) := by
  unfold transport
  infer_instance

attribute [local instance 21000] transportAdditive transportLimits transportColimits

/-- The canonical derived comparison for an exact commuting square.
Source: Stacks 015F (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def derivedSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (rho : restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ⋙
        transport e ≅ transport e' ⋙
          restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)) :
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).mapDerivedCategory ⋙
        (transport e).mapDerivedCategory ≅
      (transport e').mapDerivedCategory ⋙
        (restrictScalars
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso rho ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Abstract comparison data with its specified normalization predicate.
Source: Stacks 03D7, 015F and 06YY
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
structure ScalarComparisonData
    (X0 : Sort*)
    (X1 : Sort*)
    (X2 : Sort*)
    (P : ∀ (restriction : X0) (ordinary : X1) (derived : X2), Prop) where
  restriction : X0
  ordinary : X1
  derived : X2
  conditions : P restriction ordinary derived

/-- Normalized scalar comparison for one commuting coefficient square. The Hom
identities identify the entire adjunctions and therefore both their units and counits.
Source: Stacks 03D7, 03EK, 06YY, 07A6
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def ScalarSquareConditions {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (A : SystemScalarModel a) (B : SystemScalarModel b)
    (restriction : restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ⋙
      transport e ≅ transport e' ⋙
        restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b))
    (ordinary : A.model.E ⋙ transport e' ≅ transport e ⋙ B.model.E)
    (derived : A.model.T ⋙ (transport e').mapDerivedCategory ≅
    (transport e).mapDerivedCategory ⋙ B.model.T) : Prop :=
  (∀ (M : Modules R') (U : Cᵒᵖ) (x : M.val.obj U),
      (restriction.hom.app M).val.app U x = x) ∧
    (∀ (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (r : R'.obj.obj U),
      (ordinary.hom.app M).val.app U (systemModelTmul A.model M U r x) =
        systemModelTmul B.model ((transport e).obj M) U (e'.hom.hom.app U r) x) ∧
    (∀ (M : Modules R) (N : Modules R') (f : A.model.E.obj M ⟶ N),
      B.ordinaryAdj.homEquiv _ _ (ordinary.inv.app M ≫ (transport e').map f) =
        (transport e).map (A.ordinaryAdj.homEquiv _ _ f) ≫ restriction.hom.app N) ∧
    (∀ (P : CochainComplex (Modules R) ℤ),
      derived.hom.app (DerivedCategory.Q.obj P) ≫
          B.model.T.map ((transport e).mapDerivedCategoryFactors.hom.app P) ≫
          B.model.ε.app (((transport e).mapHomologicalComplex (.up ℤ)).obj P) =
        (transport e').mapDerivedCategory.map (A.model.ε.app P) ≫
          (transport e').mapDerivedCategoryFactors.hom.app
            ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)) ∧
    (∀ (M : DerivedCategory (Modules R)) (N : DerivedCategory (Modules R'))
      (f : A.model.T.obj M ⟶ N),
      B.adjunction.homEquiv _ _ (derived.inv.app M ≫ (transport e').mapDerivedCategory.map f) =
        (transport e).mapDerivedCategory.map (A.adjunction.homEquiv _ _ f) ≫
          (derivedSquare a b e e' restriction).hom.app N)

/-- Normalized scalar comparison for one commuting coefficient square. The Hom
identities identify the entire adjunctions and therefore both their units and counits.
Source: Stacks 03D7, 03EK, 06YY, 07A6
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
abbrev ScalarSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (A : SystemScalarModel a) (B : SystemScalarModel b) :=
  ScalarComparisonData
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ⋙
      transport e ≅ transport e' ⋙
        restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b))
    (A.model.E ⋙ transport e' ≅ transport e ⋙ B.model.E)
    (A.model.T ⋙ (transport e').mapDerivedCategory ≅
    (transport e).mapDerivedCategory ⋙ B.model.T)
    (fun restriction ordinary derived ↦
      ScalarSquareConditions a b e e' A B  restriction ordinary derived)

/-- Abstract comparison data with its specified normalization predicate.
Source: Stacks 03D7, 015F and 06YY
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
structure ReductionComparisonData
    (X0 : Sort*)
    (X1 : ∀ (ordinary : X0), Sort*)
    (X2 : ∀ (ordinary : X0), Sort*)
    (X3 : Sort*)
    (X4 : ∀ (ordinary : X0) (additive : X1 ordinary) (derived : X3), Sort*)
    (X5 : ∀ (derived : X3), Sort*)
    (P : ∀ (ordinary : X0) (additive : X1 ordinary) (evaluation : X2 ordinary)
      (derived : X3) (counit : X4 ordinary additive derived)
      (derivedEvaluation : X5 derived), Prop) where
  ordinary : X0
  additive : X1 ordinary
  evaluation : X2 ordinary
  derived : X3
  counit : X4 ordinary additive derived
  derivedEvaluation : X5 derived
  conditions : P ordinary additive evaluation derived counit derivedEvaluation

/-- The actual strict reduction, with its sheafified pure tensors, all horizontal
maps and the universal derived reduction into the ordinary derived system category.
Source: Stacks 03EK, 06YY; sequence-site refinement of lemma-section-normal-bundle--1
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def ReductionConditions (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J))
    (ordinary : Modules c.pt ⥤ StrictRingSystem B)
    [additive : ordinary.Additive]
    (evaluation : ∀ n : ℕ, ordinary ⋙ systemEvaluation B n ≅ (A (c.π.app (op n))).model.E)
    (derived : DerivedCategory (Modules c.pt) ⥤ DerivedCategory (StrictRingSystem B))
    (counit : DerivedCategory.Q ⋙ derived ⟶
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (derivedEvaluation : ∀ n : ℕ,
    derived ⋙ derivedSystemEvaluation B n ≅ (A (c.π.app (op n))).model.T) : Prop :=
  (∀ (M : Modules c.pt) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
      (r : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
      ((evaluation m).hom.app M).val.app U
        (((ordinary.obj M).transition h).val.app U
          (((evaluation n).inv.app M).val.app U
            (systemModelTmul (A (c.π.app (op n))).model M U r x))) =
        systemModelTmul (A (c.π.app (op m))).model M U
          ((B.map (homOfLE h).op).hom.app U r) x) ∧
    (derived.IsLeftDerivedFunctor counit (HomologicalComplex.quasiIso _ (.up ℤ))) ∧
    (Functor.HasPointwiseLeftDerivedFunctor
      (ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (HomologicalComplex.quasiIso _ (.up ℤ))) ∧
    (∀ (P : CochainComplex (Modules c.pt) ℤ),
      P.IsKFlatIndependentCoefficients → (∀ i : ℤ, IsFlatOnSite (R := c.pt) (P.X i)) →
        IsIso (counit.app P)) ∧
    (∀ (n : ℕ) (P : CochainComplex (Modules c.pt) ℤ),
      (derivedEvaluation n).hom.app (DerivedCategory.Q.obj P) ≫
          (A (c.π.app (op n))).model.ε.app P =
        (derivedSystemEvaluation B n).map (counit.app P) ≫
          (systemEvaluation B n).mapDerivedCategoryFactors.hom.app
            ((ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (evaluation n) (.up ℤ)).hom.app P))

/-- The actual strict reduction, with its sheafified pure tensors, all horizontal
maps and the universal derived reduction into the ordinary derived system category.
Source: Stacks 03EK, 06YY; sequence-site refinement of lemma-section-normal-bundle--1
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
abbrev Reduction (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) :=
  ReductionComparisonData
    (Modules c.pt ⥤ StrictRingSystem B)
    (fun ordinary ↦
      ordinary.Additive)
    (fun ordinary ↦
      ∀ n : ℕ, ordinary ⋙ systemEvaluation B n ≅ (A (c.π.app (op n))).model.E)
    (DerivedCategory (Modules c.pt) ⥤ DerivedCategory (StrictRingSystem B))
    (fun ordinary additive derived ↦
      letI := additive; DerivedCategory.Q ⋙ derived ⟶
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (fun derived ↦
      ∀ n : ℕ,
    derived ⋙ derivedSystemEvaluation B n ≅ (A (c.π.app (op n))).model.T)
    (fun ordinary additive evaluation derived counit derivedEvaluation ↦
      ReductionConditions B c A (additive := additive) ordinary evaluation derived counit
        derivedEvaluation)

/-- The reduction's recorded additive structure.
Source: Stacks 03EK (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
instance Reduction.additive (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (D : Reduction B c A) : D.ordinary.Additive :=
  ReductionComparisonData.additive D

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard derivedSquare systemModelTmul
  Functor.mapDerivedCategoryNatIso
  DerivedCategory.Q DerivedCategory.Qh DerivedCategory.quotientCompQhIso

private theorem derivedSquare_eq {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (ρ : restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ⋙
        transport e ≅ transport e' ⋙
          restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)) :
    derivedSquare a b e e' ρ = Functor.mapDerivedCategorySquareIso ρ := by
  unfold derivedSquare
  rfl

private def scalarRestrictionSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom) :
    restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ⋙
        transport e ≅ transport e' ⋙
          restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b) := by
  have h' : e.inv ≫ a = b ≫ e'.inv := by
    apply (cancel_epi e.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [h]
    simp
  exact systemScalarRestrictionComposition e.inv a (e.inv ≫ a) rfl ≪≫
    (systemScalarRestrictionComposition b e'.inv (e.inv ≫ a) h').symm

private def transportInverse {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    transport a ⋙ transport a.symm ≅ 𝟭 (Modules R) :=
  systemScalarRestrictionComposition a.hom a.inv (𝟙 R) (by simp) ≪≫
    systemScalarRestrictionUnit (𝟙 R) rfl


private def scalarTransportEquivalence {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    Modules R ≌ Modules S where
  functor := transport a
  inverse := transport a.symm
  unitIso := (transportInverse a).symm
  counitIso := transportInverse a.symm
  functor_unitIso_comp := by
    intro M
    ext U x
    rfl

private theorem normalizedComparison_exists
    {A₀ B₀ C₀ D₀ : Type*} [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    {L : A₀ ⥤ B₀} {U : B₀ ⥤ A₀} {L' : C₀ ⥤ D₀} {U' : D₀ ⥤ C₀}
    (a : L ⊣ U) (b : L' ⊣ U') (G : A₀ ⥤ C₀) (H : B₀ ⥤ D₀)
    [G.IsEquivalence] [H.IsEquivalence] (ρ : U ⋙ G ≅ H ⋙ U') :
    ∃! j : L ⋙ H ≅ G ⋙ L', (mateEquiv a b j.inv).natTrans = ρ.hom := by
  obtain ⟨j, hj, hu, _⟩ := exists_equivalenceAdjunctionComparison
    G.asEquivalence H.asEquivalence a b ρ
  exact ⟨j, hj, hu⟩

private def normalizedComparison
    {A₀ B₀ C₀ D₀ : Type*} [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    {L : A₀ ⥤ B₀} {U : B₀ ⥤ A₀} {L' : C₀ ⥤ D₀} {U' : D₀ ⥤ C₀}
    (a : L ⊣ U) (b : L' ⊣ U') (G : A₀ ⥤ C₀) (H : B₀ ⥤ D₀)
    [G.IsEquivalence] [H.IsEquivalence] (ρ : U ⋙ G ≅ H ⋙ U') :
    L ⋙ H ≅ G ⋙ L' :=
  (normalizedComparison_exists a b G H ρ).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedComparison_inv
    {A₀ B₀ C₀ D₀ : Type*} [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    {L : A₀ ⥤ B₀} {U : B₀ ⥤ A₀} {L' : C₀ ⥤ D₀} {U' : D₀ ⥤ C₀}
    (a : L ⊣ U) (b : L' ⊣ U') (G : A₀ ⥤ C₀) (H : B₀ ⥤ D₀)
    [G.IsEquivalence] [H.IsEquivalence] (ρ : U ⋙ G ≅ H ⋙ U') :
    (normalizedComparison a b G H ρ).inv = ((mateEquiv a b).symm ρ.hom).natTrans := by
  have hm := (normalizedComparison_exists a b G H ρ).exists.choose_spec
  change mateEquiv a b (normalizedComparison a b G H ρ).inv = ρ.hom at hm
  have he := congrArg (mateEquiv a b).symm hm
  simpa only [Equiv.symm_apply_apply] using congrArg TwoSquare.natTrans he

private instance transportIsEquivalence {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    (transport a).IsEquivalence := (scalarTransportEquivalence a).isEquivalence_functor

private def ordinaryScalarSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b) :
    A.model.E ⋙ transport e' ≅ transport e ⋙ B.model.E :=
  normalizedComparison A.ordinaryAdj B.ordinaryAdj (transport e)
    (transport e') (scalarRestrictionSquare a b e e' h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryScalarSquare_inv {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b) :
    (ordinaryScalarSquare a b e e' h A B).inv =
      ((mateEquiv A.ordinaryAdj B.ordinaryAdj).symm
        (scalarRestrictionSquare a b e e' h).hom).natTrans :=
  normalizedComparison_inv A.ordinaryAdj B.ordinaryAdj _ _ _

private theorem ordinaryScalarSquare_transpose {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b)
    (M : Modules R) (N : Modules R') (f : A.model.E.obj M ⟶ N) :
    B.ordinaryAdj.homEquiv _ _
        ((ordinaryScalarSquare a b e e' h A B).inv.app M ≫ (transport e').map f) =
      (transport e).map (A.ordinaryAdj.homEquiv _ _ f) ≫
        (scalarRestrictionSquare a b e e' h).hom.app N := by
  rw [ordinaryScalarSquare_inv]
  exact adjunctionMate_transpose A.ordinaryAdj B.ordinaryAdj
    (scalarRestrictionSquare a b e e' h).hom M N f

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryScalarSquare_tmul {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b)
    (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (r : R'.obj.obj U) :
    ((ordinaryScalarSquare a b e e' h A B).hom.app M).val.app U
        (systemModelTmul A.model M U r x) =
      systemModelTmul B.model ((transport e).obj M) U (e'.hom.hom.app U r) x := by
  let ι := ordinaryScalarSquare a b e e' h A B
  let ρ := scalarRestrictionSquare a b e e' h
  have hu := unit_mateEquiv_symm A.ordinaryAdj B.ordinaryAdj ρ.hom M
  change (transport e).map (A.ordinaryAdj.unit.app M) ≫ ρ.hom.app (A.model.E.obj M) =
    B.ordinaryAdj.unit.app ((transport e).obj M) ≫
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)).map
        ((((mateEquiv A.ordinaryAdj B.ordinaryAdj).symm
          (scalarRestrictionSquare a b e e' h).hom).natTrans).app M) at hu
  rw [← ordinaryScalarSquare_inv a b e e' h A B] at hu
  change (transport e).map (A.ordinaryAdj.unit.app M) ≫ ρ.hom.app (A.model.E.obj M) =
    B.ordinaryAdj.unit.app ((transport e).obj M) ≫
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)).map
        (ι.inv.app M) at hu
  have hunit :
      (transport e).map (A.ordinaryAdj.unit.app M) ≫ ρ.hom.app (A.model.E.obj M) ≫
        (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)).map
          (ι.hom.app M) = B.ordinaryAdj.unit.app ((transport e).obj M) := by
    rw [← Category.assoc, hu, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app]
    erw [(restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)).map_id, Category.comp_id]
  have hx := congrArg (fun f ↦ f.val.app U x) hunit
  change (ι.hom.app M).val.app U ((A.ordinaryAdj.unit.app M).val.app U x) =
    (B.ordinaryAdj.unit.app ((transport e).obj M)).val.app U x at hx
  rw [A.unit_normalized, B.unit_normalized] at hx
  have he : e'.inv.hom.app U (e'.hom.hom.app U r) = r :=
    congrArg (fun f ↦ f.hom.app U r) e'.hom_inv_id
  have hs := ((ι.hom.app M).val.app U).hom.map_smul (e'.hom.hom.app U r)
    (systemModelTmul A.model M U 1 x)
  change (ι.hom.app M).val.app U
      ((e'.inv.hom.app U (e'.hom.hom.app U r)) •
        (show (A.model.E.obj M).val.obj U from systemModelTmul A.model M U 1 x)) = _ at hs
  rw [he] at hs
  change (ι.hom.app M).val.app U _ = _
  have hx' : (ι.hom.app M).val.app U
      (systemModelTmul A.model M U 1 x) =
        systemModelTmul B.model ((transport e).obj M) U 1 x := hx
  change (ι.hom.app M).val.app U
      (r • (show (A.model.E.obj M).val.obj U from systemModelTmul A.model M U 1 x)) =
    (e'.hom.hom.app U r) • (show (B.model.E.obj ((transport e).obj M)).val.obj U from
      (ι.hom.app M).val.app U (systemModelTmul A.model M U 1 x)) at hs
  rw [hx'] at hs
  simpa only [systemModelTmul, one_smul] using hs

attribute [local irreducible] ordinaryScalarSquare

private def derivedScalarSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b) :
    A.model.T ⋙ (transport e').mapDerivedCategory ≅
      (transport e).mapDerivedCategory ⋙ B.model.T :=
  normalizedComparison A.adjunction B.adjunction (transport e).mapDerivedCategory
    (transport e').mapDerivedCategory (derivedSquare a b e e' (scalarRestrictionSquare a b e e' h))

private theorem invertComparisonForward
    {D : Type*} [Category D] {W X Y Z U V : D} (α : W ≅ X) (β : Y ≅ Z)
    (f₁ : W ⟶ U) (f₂ : U ⟶ Y) (g₁ : X ⟶ V) (g₂ : V ⟶ Z)
    (h : α.inv ≫ f₁ ≫ f₂ = g₁ ≫ g₂ ≫ β.inv) :
    α.hom ≫ g₁ ≫ g₂ = f₁ ≫ f₂ ≫ β.hom := by
  apply (cancel_epi α.inv).1
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [Category.assoc α.inv f₁ f₂, h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedScalarSquare_inv {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b) :
    (derivedScalarSquare a b e e' h A B).inv =
      ((mateEquiv A.adjunction B.adjunction).symm
        (derivedSquare a b e e' (scalarRestrictionSquare a b e e' h)).hom).natTrans :=
  normalizedComparison_inv A.adjunction B.adjunction _ _ _

private theorem derivedScalarSquare_transpose {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b)
    (M : DerivedCategory (Modules R)) (N : DerivedCategory (Modules R'))
    (f : A.model.T.obj M ⟶ N) :
    B.adjunction.homEquiv _ _
        ((derivedScalarSquare a b e e' h A B).inv.app M ≫
          (transport e').mapDerivedCategory.map f) =
      (transport e).mapDerivedCategory.map (A.adjunction.homEquiv _ _ f) ≫
        (derivedSquare a b e e' (scalarRestrictionSquare a b e e' h)).hom.app N := by
  rw [derivedScalarSquare_inv]
  exact adjunctionMate_transpose A.adjunction B.adjunction
    (derivedSquare a b e e' (scalarRestrictionSquare a b e e' h)).hom M N f

attribute [local irreducible] derivedScalarSquare

private theorem derivedMate_isoComparison
    {A₀ B₀ C₀ D₀ A₁ B₁ C₁ D₁ : Type*}
    [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    [Category A₁] [Category B₁] [Category C₁] [Category D₁]
    {L : A₀ ⥤ B₀} {R : B₀ ⥤ A₀} {L' : C₀ ⥤ D₀} {R' : D₀ ⥤ C₀}
    {LD : A₁ ⥤ B₁} {RD : B₁ ⥤ A₁} {LD' : C₁ ⥤ D₁} {RD' : D₁ ⥤ C₁}
    {G : A₀ ⥤ C₀} {H : B₀ ⥤ D₀} {GD : A₁ ⥤ C₁} {HD : B₁ ⥤ D₁}
    {QA : A₀ ⥤ A₁} {QB : B₀ ⥤ B₁} {QC : C₀ ⥤ C₁} {QD : D₀ ⥤ D₁}
    (a : L ⊣ R) (b : L' ⊣ R') (ad : LD ⊣ RD) (bd : LD' ⊣ RD')
    (ε : QA ⋙ LD ⟶ L ⋙ QB) (ε' : QC ⋙ LD' ⟶ L' ⋙ QD)
    (ρ : QB ⋙ RD ≅ R ⋙ QA) (ρ' : QD ⋙ RD' ≅ R' ⋙ QC)
    (γ : QA ⋙ GD ≅ G ⋙ QC) (η : QB ⋙ HD ≅ H ⋙ QD)
    (ha : ∀ P K (f : L.obj P ⟶ K),
      ad.homEquiv _ _ (ε.app P ≫ QB.map f) = QA.map (a.homEquiv _ _ f) ≫ ρ.inv.app K)
    (hb : ∀ P K (f : L'.obj P ⟶ K),
      bd.homEquiv _ _ (ε'.app P ≫ QD.map f) = QC.map (b.homEquiv _ _ f) ≫ ρ'.inv.app K)
    (τ : R ⋙ G ⟶ H ⋙ R') (τD : RD ⋙ GD ⟶ HD ⋙ RD')
    (hτ : ∀ K, τD.app (QB.obj K) ≫ RD'.map (η.hom.app K) ≫ ρ'.hom.app (H.obj K) =
      GD.map (ρ.hom.app K) ≫ γ.hom.app (R.obj K) ≫ QC.map (τ.app K))
    (i : L ⋙ H ≅ G ⋙ L') (j : LD ⋙ HD ≅ GD ⋙ LD')
    (hi : ∀ P, b.homEquiv _ _ (i.inv.app P) = G.map (a.unit.app P) ≫ τ.app (L.obj P))
    (hj : j.inv = ((mateEquiv ad bd).symm τD).natTrans) (P : A₀) :
    j.hom.app (QA.obj P) ≫ LD'.map (γ.hom.app P) ≫ ε'.app (G.obj P) =
      HD.map (ε.app P) ≫ η.hom.app (L.obj P) ≫ QD.map (i.hom.app P) := by
  have ht := derivedMate_comparison a b ad bd ε ε' ρ ρ' γ η ha hb τ τD hτ i.inv hi P
  change ((mateEquiv ad bd).symm τD).natTrans.app _ ≫ _ ≫ _ = _ at ht
  rw [← hj] at ht
  exact invertComparisonForward (j.app (QA.obj P)) (QD.mapIso (i.app P)) _ _ _ _ ht

private theorem cochainMateUnit
    {A₀ B₀ C₀ D₀ : Type*} [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    [Preadditive A₀] [Preadditive B₀] [Preadditive C₀] [Preadditive D₀]
    {L : A₀ ⥤ B₀} {R : B₀ ⥤ A₀} {L' : C₀ ⥤ D₀} {R' : D₀ ⥤ C₀}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
    (a : L ⊣ R) (b : L' ⊣ R') (G : A₀ ⥤ C₀) (H : B₀ ⥤ D₀)
    [G.Additive] [H.Additive] (i : L ⋙ H ≅ G ⋙ L') (τ : R ⋙ G ⟶ H ⋙ R')
    (hi : ∀ P, b.homEquiv _ _ (i.inv.app P) = G.map (a.unit.app P) ≫ τ.app (L.obj P))
    (K : CochainComplex A₀ ℤ) :
    (b.mapHomologicalComplex (.up ℤ)).homEquiv
        ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((H.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj K))
        ((NatIso.mapHomologicalComplex i (.up ℤ)).inv.app K) =
      (G.mapHomologicalComplex (.up ℤ)).map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        (τ.mapHomologicalComplex (.up ℤ)).app ((L.mapHomologicalComplex (.up ℤ)).obj K) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact hi (K.X n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryScalarSquare_unit {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b) (M : Modules R) :
    B.ordinaryAdj.homEquiv _ _ ((ordinaryScalarSquare a b e e' h A B).inv.app M) =
      (transport e).map (A.ordinaryAdj.unit.app M) ≫
        (scalarRestrictionSquare a b e e' h).hom.app (A.model.E.obj M) := by
  have ht := ordinaryScalarSquare_transpose a b e e' h A B M (A.model.E.obj M) (𝟙 _)
  erw [(transport e').map_id] at ht
  erw [Category.comp_id] at ht
  dsimp only [Functor.comp_obj]
  simpa only [Adjunction.homEquiv_id] using ht

private theorem derivedMate_cochainIsoComparison
    {A₀ B₀ C₀ D₀ : Type*} [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    [Abelian A₀] [Abelian B₀] [Abelian C₀] [Abelian D₀]
    [HasDerivedCategory A₀] [HasDerivedCategory B₀]
    [HasDerivedCategory C₀] [HasDerivedCategory D₀]
    {L : A₀ ⥤ B₀} {R : B₀ ⥤ A₀} {L' : C₀ ⥤ D₀} {R' : D₀ ⥤ C₀}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    (a : L ⊣ R) (b : L' ⊣ R') (G : A₀ ⥤ C₀) (H : B₀ ⥤ D₀)
    [G.Additive] [H.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {T : DerivedCategory A₀ ⥤ DerivedCategory B₀}
    {T' : DerivedCategory C₀ ⥤ DerivedCategory D₀}
    (ad : T ⊣ R.mapDerivedCategory) (bd : T' ⊣ R'.mapDerivedCategory)
    (ε : DerivedCategory.Q ⋙ T ⟶ L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ε' : DerivedCategory.Q ⋙ T' ⟶ L'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ha : ∀ P K (f : (L.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      ad.homEquiv _ _ (ε.app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
          R.mapDerivedCategoryFactors.inv.app K)
    (hb : ∀ P K (f : (L'.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      bd.homEquiv _ _ (ε'.app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((b.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
          R'.mapDerivedCategoryFactors.inv.app K)
    (ρ : R ⋙ G ≅ H ⋙ R') (i : L ⋙ H ≅ G ⋙ L')
    (j : T ⋙ H.mapDerivedCategory ≅ G.mapDerivedCategory ⋙ T')
    (hi : ∀ P, b.homEquiv _ _ (i.inv.app P) = G.map (a.unit.app P) ≫ ρ.hom.app (L.obj P))
    (hj : j.inv = ((mateEquiv ad bd).symm (Functor.mapDerivedCategorySquareIso ρ).hom).natTrans)
    (P : CochainComplex A₀ ℤ) :
    j.hom.app (DerivedCategory.Q.obj P) ≫ T'.map (G.mapDerivedCategoryFactors.hom.app P) ≫
        ε'.app ((G.mapHomologicalComplex (.up ℤ)).obj P) =
      H.mapDerivedCategory.map (ε.app P) ≫
        H.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex i (.up ℤ)).hom.app P) := by
  apply derivedMate_isoComparison (a.mapHomologicalComplex (.up ℤ))
    (b.mapHomologicalComplex (.up ℤ)) ad bd ε ε'
    R.mapDerivedCategoryFactors R'.mapDerivedCategoryFactors
    G.mapDerivedCategoryFactors H.mapDerivedCategoryFactors ha hb
    (ρ.hom.mapHomologicalComplex (.up ℤ)) (Functor.mapDerivedCategorySquareIso ρ).hom
    (Functor.exactSquare_fac ρ) (NatIso.mapHomologicalComplex i (.up ℤ)) j
    (cochainMateUnit a b G H i ρ.hom hi) hj P

private theorem derivedScalarSquare_rep {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b)
    (P : CochainComplex (Modules R) ℤ) :
    (derivedScalarSquare a b e e' h A B).hom.app (DerivedCategory.Q.obj P) ≫
        B.model.T.map ((transport e).mapDerivedCategoryFactors.hom.app P) ≫
        B.model.ε.app (((transport e).mapHomologicalComplex (.up ℤ)).obj P) =
      (transport e').mapDerivedCategory.map (A.model.ε.app P) ≫
        (transport e').mapDerivedCategoryFactors.hom.app
          ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryScalarSquare a b e e' h A B)
            (.up ℤ)).hom.app P) := by
  exact derivedMate_cochainIsoComparison A.ordinaryAdj B.ordinaryAdj (transport e) (transport e')
    A.adjunction B.adjunction A.model.ε B.model.ε A.transpose B.transpose
    (scalarRestrictionSquare a b e e' h) (ordinaryScalarSquare a b e e' h A B)
    (derivedScalarSquare a b e e' h A B) (ordinaryScalarSquare_unit a b e e' h A B)
    (by rw [derivedScalarSquare_inv, derivedSquare_eq]) P

private def scalarSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b) :
    ScalarSquare a b e e' A B where
  restriction := scalarRestrictionSquare a b e e' h
  ordinary := ordinaryScalarSquare a b e e' h A B
  derived := derivedScalarSquare a b e e' h A B
  conditions := ⟨(by intro M U x; rfl),
    ordinaryScalarSquare_tmul a b e e' h A B,
    ordinaryScalarSquare_transpose a b e e' h A B,
    derivedScalarSquare_rep a b e e' h A B,
    derivedScalarSquare_transpose a b e e' h A B⟩

private def reductionTransition (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (M : Modules c.pt) {m n : ℕ} (h : m ≤ n) :
    (A (c.π.app (op n))).model.E.obj M ⟶
      (systemRestriction B h).obj ((A (c.π.app (op m))).model.E.obj M) :=
  (A (B.map (homOfLE h).op)).ordinaryAdj.homEquiv _ _
    ((systemScalarModelComposition (c.w (homOfLE h).op).symm
      (A (c.π.app (op n))) (A (B.map (homOfLE h).op))
      (A (c.π.app (op m)))).hom.app M)

private theorem reductionTransition_tmul
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (M : Modules c.pt) {m n : ℕ} (h : m ≤ n)
    (U : Cᵒᵖ) (r : (B.obj (op n)).obj.obj U) (x : M.val.obj U) :
    (reductionTransition B c A M h).val.app U
        (systemModelTmul (A (c.π.app (op n))).model M U r x) =
      systemModelTmul (A (c.π.app (op m))).model M U
        ((B.map (homOfLE h).op).hom.app U r) x := by
  dsimp only [reductionTransition]
  rw [Adjunction.homEquiv_unit]
  change ((systemScalarModelComposition (c.w (homOfLE h).op).symm
      (A (c.π.app (op n))) (A (B.map (homOfLE h).op))
      (A (c.π.app (op m)))).hom.app M).val.app U
    (((A (B.map (homOfLE h).op)).ordinaryAdj.unit.app
      ((A (c.π.app (op n))).model.E.obj M)).val.app U _) = _
  rw [(A (B.map (homOfLE h).op)).unit_normalized]
  rw [systemScalarModelComposition_tmul]
  simp only [one_mul]

private def reductionObj (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (M : Modules c.pt) : StrictRingSystem B where
  level n := (A (c.π.app (op n))).model.E.obj M
  transition := reductionTransition B c A M
  identity := by
    intro n U x
    let η := systemScalarRestrictionUnit (B.map (homOfLE (Nat.le_refl n)).op)
      (B.map_id (op n))
    have he : reductionTransition B c A M (Nat.le_refl n) =
        η.inv.app ((A (c.π.app (op n))).model.E.obj M) := by
      apply systemScalarModel_hom_ext (A (c.π.app (op n)))
      intro V y
      change (reductionTransition B c A M (Nat.le_refl n)).val.app V _ =
        systemModelTmul (A (c.π.app (op n))).model M V 1 y
      simpa only [map_one] using
        reductionTransition_tmul B c A M (Nat.le_refl n) V 1 y
    exact congrArg (fun f ↦ f.val.app U x) he
  compose := by
    intro l m n h k U x
    have hc : B.map (homOfLE (h.trans k)).op =
        B.map (homOfLE k).op ≫ B.map (homOfLE h).op := by
      rw [← B.map_comp]
      rfl
    let η := systemScalarRestrictionComposition _ _ _ hc
    have he : reductionTransition B c A M (h.trans k) =
        reductionTransition B c A M k ≫
          (systemRestriction B k).map (reductionTransition B c A M h) ≫
          η.hom.app ((A (c.π.app (op l))).model.E.obj M) := by
      apply systemScalarModel_hom_ext (A (c.π.app (op n)))
      intro V y
      change (reductionTransition B c A M (h.trans k)).val.app V _ =
        (reductionTransition B c A M h).val.app V
          ((reductionTransition B c A M k).val.app V _)
      rw [reductionTransition_tmul, reductionTransition_tmul]
      simp only [map_one]
      rw [reductionTransition_tmul]
      simp only [map_one]
      rfl
    exact congrArg (fun f ↦ f.val.app U x) he

private def reductionMap (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) {M N : Modules c.pt} (f : M ⟶ N) :
    reductionObj B c A M ⟶ reductionObj B c A N where
  app n := (A (c.π.app (op n))).model.E.map f
  comm := by
    intro m n h
    apply systemScalarModel_hom_ext (A (c.π.app (op n)))
    intro U x
    change (reductionTransition B c A N h).val.app U
        (((A (c.π.app (op n))).model.E.map f).val.app U _) =
      ((A (c.π.app (op m))).model.E.map f).val.app U
        ((reductionTransition B c A M h).val.app U _)
    rw [systemScalarModel_map_tmul, reductionTransition_tmul,
      reductionTransition_tmul, systemScalarModel_map_tmul]

private def reductionFunctor (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) : Modules c.pt ⥤ StrictRingSystem B where
  obj := reductionObj B c A
  map := reductionMap B c A
  map_id M := by
    apply strictRingSystem_hom_ext
    intro n
    exact (A (c.π.app (op n))).model.E.map_id M
  map_comp f g := by
    apply strictRingSystem_hom_ext
    intro n
    exact (A (c.π.app (op n))).model.E.map_comp f g

private instance reductionFunctorAdditive
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) : (reductionFunctor B c A).Additive where
  map_add := by
    intro M N f g
    apply strictRingSystem_hom_ext
    intro n
    change (A (c.π.app (op n))).model.E.map (f + g) = _
    rw [Functor.map_add]
    exact ((systemEvaluation B n).map_add
      (f := (reductionFunctor B c A).map f) (g := (reductionFunctor B c A).map g)).symm

private def reductionEvaluation (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (n : ℕ) :
    reductionFunctor B c A ⋙ systemEvaluation B n ≅ (A (c.π.app (op n))).model.E :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N f
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

private theorem reductionTransition_normalized
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (M : Modules c.pt) {m n : ℕ} (h : m ≤ n)
    (U : Cᵒᵖ) (r : (B.obj (op n)).obj.obj U) (x : M.val.obj U) :
    (((reductionEvaluation B c A m).hom.app M).val.app U
      ((((reductionFunctor B c A).obj M).transition h).val.app U
        (((reductionEvaluation B c A n).inv.app M).val.app U
          (systemModelTmul (A (c.π.app (op n))).model M U r x)))) =
      systemModelTmul (A (c.π.app (op m))).model M U
        ((B.map (homOfLE h).op).hom.app U r) x :=
  reductionTransition_tmul B c A M h U r x

attribute [local irreducible] reductionFunctor

private structure DerivedReductionPackage
    (T : Sort*) (E : T → Sort*) (V : T → Sort*)
    (P : ∀ t, E t → V t → Prop) where
  derived : T
  counit : E derived
  derivedEvaluation : V derived
  conditions : P derived counit derivedEvaluation

private abbrev ReductionDerivedData
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J))
    (E : Modules c.pt ⥤ StrictRingSystem B) [E.Additive]
    (evaluation : ∀ n : ℕ, E ⋙ systemEvaluation B n ≅ (A (c.π.app (op n))).model.E) :=
  DerivedReductionPackage
    (DerivedCategory (Modules c.pt) ⥤ DerivedCategory (StrictRingSystem B))
    (fun derived ↦
      DerivedCategory.Q ⋙ derived ⟶
    E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (fun derived ↦
      ∀ n : ℕ,
    derived ⋙ derivedSystemEvaluation B n ≅ (A (c.π.app (op n))).model.T)
    (fun derived counit derivedEvaluation ↦
      (derived.IsLeftDerivedFunctor counit (HomologicalComplex.quasiIso _ (.up ℤ))) ∧
      (Functor.HasPointwiseLeftDerivedFunctor
    (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso _ (.up ℤ))) ∧
      (∀ P : CochainComplex (Modules c.pt) ℤ,
    P.IsKFlatIndependentCoefficients → (∀ i : ℤ, IsFlatOnSite (R := c.pt) (P.X i)) →
      IsIso (counit.app P)) ∧
      (∀ (n : ℕ) (P : CochainComplex (Modules c.pt) ℤ),
    (derivedEvaluation n).hom.app (DerivedCategory.Q.obj P) ≫
        (A (c.π.app (op n))).model.ε.app P =
      (derivedSystemEvaluation B n).map (counit.app P) ≫
        (systemEvaluation B n).mapDerivedCategoryFactors.hom.app
          ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (evaluation n) (.up ℤ)).hom.app P)))

private abbrev ReductionDerivedModel
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) :=
  ReductionDerivedData B c A (reductionFunctor B c A) (reductionEvaluation B c A)

private abbrev reduction (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (D : ReductionDerivedModel B c A) :
    Reduction B c A where
  ordinary := reductionFunctor B c A
  additive := reductionFunctorAdditive B c A
  evaluation := reductionEvaluation B c A
  derived := D.derived
  counit := D.counit
  derivedEvaluation := D.derivedEvaluation
  conditions := ⟨reductionTransition_normalized B c A, D.conditions.1,
    D.conditions.2.1, D.conditions.2.2.1, D.conditions.2.2.2⟩

end SheafOfModules.QuotientIsoTransport
