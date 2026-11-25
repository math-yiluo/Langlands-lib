/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
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
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.Algebra.Homology.Strict.StrictProjectionLimitData
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.CategoryTheory.Localization.Adjunction
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Finite-free scalar extension and strict derived towers

Source: Stacks Project, algebraization.tex, Tag 0A0E (application); sites-cohomology.tex,
Tag 0941 (resolved Roos triangle); derived.tex, Tags 070I, 08BJ, 0BK6.
(blueprint: lem-weil-pbc-finite-free-strict-tower-transport).

The helpers specify canonical maps and their cochain factorizations. Positive
levels are indexed by `n : ℕ` meaning level `n + 1`. All complexes are unbounded.
The existing `StrictProjectionLimitData` packages the recorded total right derived limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v r w uA vA uB vB
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open SheafOfModules

namespace CategoryTheory

/-- The ordinary inverse-limit functor on cochain complexes of strict towers.
Source: Stacks 0941 (blueprint: lem-weil-pbc-finite-free-strict-tower-transport). -/
abbrev strictTowerLimitComplex (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] :=
  (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The canonical inclusion of the ordinary strict limit into the product of evaluations.
Source: Stacks 0941 (blueprint: lem-weil-pbc-finite-free-strict-tower-transport). -/
def strictTowerLimitInclusion {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (strictTowerLimitComplex A).obj I ⟶ ∏ᶜ (fun n : ℕ ↦ I.asFunctor.obj (op n)) :=
  Pi.lift (fun n : ℕ ↦
    (NatTrans.mapHomologicalComplex (lim.π (op n)) (ComplexShape.up ℤ)).app I)

/-- Product comparison from a cochain tower to its derived evaluations, including the
specified evaluation factorization of the strict-limit interface.
Source: Stacks 0941 (blueprint: lem-weil-pbc-finite-free-strict-tower-transport). -/
def strictTowerResolvedProduct {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    (L : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q)
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    DerivedCategory.Q.obj (∏ᶜ (fun n : ℕ ↦ I.asFunctor.obj (op n))) ⟶
      ∏ᶜ (fun n : ℕ ↦ (L.ev.obj (DerivedCategory.Q.obj I)).obj (op n)) :=
  piComparison DerivedCategory.Q (fun n : ℕ ↦ I.asFunctor.obj (op n)) ≫
    Limits.Pi.map (fun n : ℕ ↦ (L.evaluation.inv.app I).app (op n))

/-- Normalization of the whole Roos triangle on injective-term K-injective towers.
The last equation fixes the connecting arrow as the actual short-exact-sequence boundary.
It does not choose a completion of an abstract triangle.
Source: Stacks 0941 (blueprint: lem-weil-pbc-finite-free-strict-tower-transport). -/
def strictTowerRoosNormalized
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    (L : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q) : Prop :=
  (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ),
    L.eta.app X ≫ L.p (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map (strictTowerLimitInclusion X) ≫ strictTowerResolvedProduct L X) ∧
  ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), I.IsKInjective →
    (∀ k : ℤ, Injective (I.X k)) →
    ∀ (h : strictTowerLimitInclusion I ≫
        towerTransitionEndomorphism
          (fun n : ℕ ↦ I.asFunctor.map (homOfLE (Nat.le_succ n)).op) = 0)
      (hs : (ShortComplex.mk (strictTowerLimitInclusion I)
        (towerTransitionEndomorphism
          (fun n : ℕ ↦ I.asFunctor.map (homOfLE (Nat.le_succ n)).op)) h).ShortExact),
      strictTowerResolvedProduct L I ≫ L.delta (DerivedCategory.Q.obj I) =
        DerivedCategory.triangleOfSESδ hs ≫ (L.eta.app I)⟦(1 : ℤ)⟧'

private theorem towerProductComparison_middle
    {A : Type uA} [Category.{vA} A] [Preadditive A] [HasCountableProducts A]
    {B : Type uB} [Category.{vB} B] [Preadditive B] [HasCountableProducts B]
    (G : A ⥤ B) [G.Additive] (X : ℕᵒᵖ ⥤ A) (Y : ℕᵒᵖ ⥤ B)
    (e : X ⋙ G ≅ Y) :
    G.map (towerTransitionEndomorphism
        (fun n : ℕ ↦ X.map (homOfLE (Nat.le_succ n)).op)) ≫
        piComparison G (fun n : ℕ ↦ X.obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ e.hom.app (op n)) =
      piComparison G (fun n : ℕ ↦ X.obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ e.hom.app (op n)) ≫
        towerTransitionEndomorphism
          (fun n : ℕ ↦ Y.map (homOfLE (Nat.le_succ n)).op) := by
  apply Pi.hom_ext
  intro n
  simp only [towerTransitionEndomorphism, towerProductShift, Functor.map_sub,
    Functor.map_id, Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub,
    Category.comp_id, Category.assoc, Limits.Pi.map_π, Pi.lift_comp_π,
    piComparison_comp_π_assoc]
  rw [← G.map_comp_assoc, Pi.lift_comp_π]
  rw [G.map_comp, Category.assoc]
  simp only [Limits.Pi.map_π_assoc, piComparison_comp_π_assoc]
  congr 1
  exact congrArg (G.map (Pi.π _ (n + 1)) ≫ ·)
    (e.hom.naturality (homOfLE (Nat.le_succ n)).op)

/-- Finite-free transport data with the normalized ordinary and derived comparisons,
all three Roos squares and the strict augmentation formula. `augmentation` quantifies
all maps to the ordinary limit, equivalently all compatible strict augmented towers.
Source: Stacks 0A0E, 0941 (blueprint: lem-weil-pbc-finite-free-strict-tower-transport). -/
structure FiniteFreeStrictTowerTransport
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasCountableProducts A] [HasCountableProducts B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    [HasCountableProducts (DerivedCategory.{w} B)]
    (F : A ⥤ B) [F.Additive]
    (G : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B) [G.CommShift ℤ]
    (T : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ B))
    (factors : DerivedCategory.Q ⋙ G ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (towerFactors : DerivedCategory.Q ⋙ T ≅
      (projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) where
  /-- The source total derived inverse limit with its functorial Roos triangles. -/
  source : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q
  /-- The target total derived inverse limit with its functorial Roos triangles. -/
  target : StrictProjectionLimitData B DerivedCategory.Q DerivedCategory.Q
  /-- The source total derived inverse limit is exact with its cochain shift. -/
  source_exact : ∃ (_ : source.L.CommShift ℤ), source.L.IsTriangulated
  /-- The target total derived inverse limit is exact with its cochain shift. -/
  target_exact : ∃ (_ : target.L.CommShift ℤ), target.L.IsTriangulated
  /-- Pin the source connecting arrow to the resolved short exact sequence. -/
  source_normalized : strictTowerRoosNormalized source
  /-- Pin the target connecting arrow to the resolved short exact sequence. -/
  target_normalized : strictTowerRoosNormalized target
  /-- The ordinary limit/tensor comparison. -/
  ordinary : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ F ≅
    projectionPost (I := ℕᵒᵖ) F ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B)
  /-- Its definition by ordinary limit projections. -/
  ordinary_normalized : ∀ X : ℕᵒᵖ ⥤ A, ordinary.hom.app X = limit.post X F
  /-- Canonical projection comparison for every countable family in D(A). -/
  products : ∀ M : ℕ → DerivedCategory.{w} A, IsIso (piComparison G M)
  /-- Exact termwise tensor commutes with derived evaluation. -/
  evaluation : T ⋙ target.ev ≅
    source.ev ⋙ projectionPost (I := ℕᵒᵖ) G
  /-- This is the evaluation comparison induced on actual cochain representatives. -/
  evaluation_normalized : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ),
    (target.ev.map (towerFactors.hom.app X)).app n ≫
        (target.evaluation.hom.app
          (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X)).app n ≫
        factors.inv.app (X.asFunctor.obj n) =
      (evaluation.hom.app (DerivedCategory.Q.obj X)).app n ≫
        G.map ((source.evaluation.hom.app X).app n)
  /-- The natural derived-limit comparison lambda. -/
  comparison : source.L ⋙ G ≅
    T ⋙ target.L
  /-- The defining total-derived comparison equation, for every complex. -/
  comparison_normalized : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    G.map (source.eta.app X) ≫
        comparison.hom.app (DerivedCategory.Q.obj X) =
      factors.hom.app ((strictTowerLimitComplex A).obj X) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app X) ≫
        target.eta.app
          (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X) ≫
        target.L.map (towerFactors.inv.app X)
  /-- The first square of the Roos triangles, with the canonical product comparison. -/
  roos_first : ∀ X : DerivedCategory.{w} (ℕᵒᵖ ⥤ A),
    G.map (source.p X) ≫
        piComparison G (fun n : ℕ ↦ (source.ev.obj X).obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ (evaluation.inv.app X).app (op n)) =
      comparison.hom.app X ≫
        target.p (T.obj X)
  /-- The middle square: the projection comparison intertwines one minus shift. -/
  roos_middle : ∀ X : DerivedCategory.{w} (ℕᵒᵖ ⥤ A),
    G.map (towerTransitionEndomorphism
        (fun n : ℕ ↦ (source.ev.obj X).map (homOfLE (Nat.le_succ n)).op)) ≫
        piComparison G (fun n : ℕ ↦ (source.ev.obj X).obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ (evaluation.inv.app X).app (op n)) =
      piComparison G (fun n : ℕ ↦ (source.ev.obj X).obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ (evaluation.inv.app X).app (op n)) ≫
        towerTransitionEndomorphism (fun n : ℕ ↦
          (target.ev.obj (T.obj X)).map
            (homOfLE (Nat.le_succ n)).op)
  /-- The last square, including the cochain-normalized shift comparison. -/
  roos_last : ∀ X : DerivedCategory.{w} (ℕᵒᵖ ⥤ A),
    G.map (source.delta X) ≫
        (G.commShiftIso (1 : ℤ)).hom.app (source.L.obj X) ≫
        (comparison.hom.app X)⟦(1 : ℤ)⟧' =
      piComparison G (fun n : ℕ ↦ (source.ev.obj X).obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ (evaluation.inv.app X).app (op n)) ≫
        target.delta (T.obj X)
  /-- A strict augmentation is its ordinary-limit lift z. The equation is lambda C(z)=z'. -/
  augmentation : ∀ (M : CochainComplex A ℤ) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
      (z : M ⟶ (strictTowerLimitComplex A).obj X),
    G.map (DerivedCategory.Q.map z ≫ source.eta.app X) ≫
        comparison.hom.app (DerivedCategory.Q.obj X) =
      factors.hom.app M ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map z ≫
          (NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app X) ≫
        target.eta.app
          (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X) ≫
        target.L.map (towerFactors.inv.app X)
  /-- Naturality for a map (h,v) of entire augmented towers, including the source complex. -/
  augmented_naturality : ∀ (M N : CochainComplex A ℤ)
      (X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
      (z : M ⟶ (strictTowerLimitComplex A).obj X)
      (t : N ⟶ (strictTowerLimitComplex A).obj Y)
      (h : M ⟶ N) (v : X ⟶ Y),
    z ≫ (strictTowerLimitComplex A).map v = h ≫ t →
      G.map (DerivedCategory.Q.map z ≫ source.eta.app X) ≫
          comparison.hom.app (DerivedCategory.Q.obj X) ≫
          target.L.map (T.map
            (DerivedCategory.Q.map v)) =
        G.map (DerivedCategory.Q.map h) ≫
          G.map (DerivedCategory.Q.map t ≫ source.eta.app Y) ≫
          comparison.hom.app (DerivedCategory.Q.obj Y)

private noncomputable def exactDerivedAdjunction
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    {F : A ⥤ B} {U : B ⥤ A} [F.Additive] [U.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] (adj : F ⊣ U) :
    F.mapDerivedCategory ⊣ U.mapDerivedCategory := by
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (U.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q U.mapDerivedCategory := ⟨U.mapDerivedCategoryFactors.symm⟩
  exact (adj.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso B (.up ℤ))
    F.mapDerivedCategory U.mapDerivedCategory

private noncomputable def finitePowerSelfAdjunction
    {A : Type uA} [Category.{vA} A] [Abelian A] (d : ℕ) :
    (Functor.const (Discrete (Fin d)) ⋙ (lim : (Discrete (Fin d) ⥤ A) ⥤ A)) ⊣
      (Functor.const (Discrete (Fin d)) ⋙ (lim : (Discrete (Fin d) ⥤ A) ⥤ A)) := by
  let : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
  exact Adjunction.ofNatIsoLeft
    ((constLimAdj : (Functor.const (Discrete (Fin d)) : A ⥤ _) ⊣ lim).comp colimConstAdj)
    (Functor.isoWhiskerLeft _ HasBiproductsOfShape.colimIsoLim)

private theorem finitePowerExact
    {A : Type uA} [Category.{vA} A] [Abelian A] (d : ℕ) :
    PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ A) ⥤ A)) := by
  let : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
  let : PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
      (colim : (Discrete (Fin d) ⥤ A) ⥤ A)) := inferInstance
  exact preservesFiniteColimits_of_natIso
    (Functor.isoWhiskerLeft _ HasBiproductsOfShape.colimIsoLim)

private theorem finiteCoordinatesDerivedProducts
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    [HasCountableProducts (DerivedCategory.{w} A)]
    [HasCountableProducts (DerivedCategory.{w} B)]
    (F : A ⥤ B) (U : B ⥤ A) [F.Additive] [U.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [U.ReflectsIsomorphisms] (adj : F ⊣ U) (d : ℕ)
    (e : F ⋙ U ≅ Functor.const (Discrete (Fin d)) ⋙ lim) :
    ∀ M : ℕ → DerivedCategory.{w} A, IsIso (piComparison F.mapDerivedCategory M) := by
  let P := (Functor.const (Discrete (Fin d)) : A ⥤ _) ⋙ lim
  let : P.Additive := by
    constructor
    intro X Y f g
    apply limit.hom_ext
    intro n
    simp only [P, Functor.comp_map, lim_map, limMap_π, Preadditive.add_comp,
      Functor.const_map_app, Preadditive.comp_add]
  let : PreservesFiniteLimits P := inferInstance
  let : PreservesFiniteColimits P := finitePowerExact d
  let ap := exactDerivedAdjunction (finitePowerSelfAdjunction (A := A) d)
  let au := exactDerivedAdjunction adj
  let : U.mapDerivedCategory.IsRightAdjoint := au.isRightAdjoint
  let : P.mapDerivedCategory.IsRightAdjoint := ap.isRightAdjoint
  let : U.mapDerivedCategory.ReflectsIsomorphisms :=
    { reflects := by
        intro X Y f hf
        rw [DerivedCategory.isIso_iff]
        intro n
        have : IsIso (U.map ((DerivedCategory.homologyFunctor B n).map f)) :=
          (NatIso.isIso_map_iff (U.mapDerivedCategoryHomologyFunctorIso n) f).2
            (by dsimp only [Functor.comp_map]; infer_instance)
        exact isIso_of_reflects_iso _ U }
  let : PreservesLimitsOfShape (Discrete ℕ) (F.mapDerivedCategory ⋙ U.mapDerivedCategory) :=
    preservesLimitsOfShape_of_natIso (Functor.mapDerivedCategoryCompNatIso e).symm
  let : ReflectsLimitsOfShape (Discrete ℕ) U.mapDerivedCategory :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  let : PreservesLimitsOfShape (Discrete ℕ) F.mapDerivedCategory :=
    preservesLimitsOfShape_of_reflects_of_preserves _ U.mapDerivedCategory
  intro M
  infer_instance

private theorem strictTowerEvaluationIso
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    [HasCountableProducts (DerivedCategory.{w} B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) F)]
    [PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) F)]
    (LR : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q)
    (LS : StrictProjectionLimitData B DerivedCategory.Q DerivedCategory.Q) :
    ∃ e : (projectionPost F).mapDerivedCategory ⋙ LS.ev ≅
        LR.ev ⋙ projectionPost (I := ℕᵒᵖ) F.mapDerivedCategory,
      ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ),
      (LS.ev.map ((projectionPost F).mapDerivedCategoryFactors.hom.app X)).app n ≫
          (LS.evaluation.hom.app
            (((projectionPost F).mapHomologicalComplex (.up ℤ)).obj X)).app n ≫
          F.mapDerivedCategoryFactors.inv.app (X.asFunctor.obj n) =
        (e.hom.app (DerivedCategory.Q.obj X)).app n ≫
          F.mapDerivedCategory.map ((LR.evaluation.hom.app X).app n) := by
  let Fc := (projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)
  let G := F.mapDerivedCategory
  let T := (projectionPost (I := ℕᵒᵖ) F).mapDerivedCategory
  let eX (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      (T ⋙ LS.ev).obj (DerivedCategory.Q.obj X) ≅
        (LR.ev ⋙ projectionPost G).obj (DerivedCategory.Q.obj X) :=
    LS.ev.mapIso ((projectionPost F).mapDerivedCategoryFactors.app X) ≪≫
      LS.evaluation.app (Fc.obj X) ≪≫
      Functor.isoWhiskerLeft X.asFunctor F.mapDerivedCategoryFactors.symm ≪≫
      (projectionPost G).mapIso (LR.evaluation.symm.app X)
  let ee : DerivedCategory.Q ⋙ T ⋙ LS.ev ≅
      DerivedCategory.Q ⋙ LR.ev ⋙ projectionPost G :=
    NatIso.ofComponents eX (by
      intro X Y f
      ext n
      dsimp only [Functor.comp_map, eX, Iso.trans_hom, Functor.mapIso_hom,
        NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
        Iso.symm_hom, Iso.app_hom]
      have h1 := congrArg (fun k ↦ (LS.ev.map k).app n)
        ((projectionPost F).mapDerivedCategoryFactors.hom.naturality f)
      simp only [Functor.map_comp, NatTrans.comp_app, Functor.comp_map] at h1
      have h2 := congrArg (fun k ↦ k.app n) (LS.evaluation.hom.naturality (Fc.map f))
      simp only [NatTrans.comp_app, Functor.comp_map] at h2
      have h3 := F.mapDerivedCategoryFactors.inv.naturality
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app n)
      dsimp only [Functor.comp_map] at h3
      have h4 := congrArg (fun k ↦ G.map (k.app n)) (LR.evaluation.inv.naturality f)
      simp only [NatTrans.comp_app, Functor.map_comp, Functor.comp_map] at h4
      simp only [Category.assoc]
      erw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3]
      change _ = _ ≫ _ ≫ _ ≫ G.map ((LR.evaluation.inv.app X).app n) ≫
        G.map ((LR.ev.map (DerivedCategory.Q.map f)).app n)
      erw [h4]
      rfl)
  let e := Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) _ _
    (T ⋙ LS.ev) (LR.ev ⋙ projectionPost G) ee
  refine ⟨e, ?_⟩
  intro X n
  simp only [e, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    Localization.Lifting.iso, Iso.refl_hom, Iso.refl_inv]
  dsimp only [ee, NatIso.ofComponents_hom_app, eX, Iso.trans_hom,
    Functor.mapIso_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Iso.app_hom]
  simp only [NatTrans.id_app, Category.comp_id, Category.assoc]
  dsimp only [projectionPost, Functor.whiskeringRight_obj_map, Functor.whiskerRight_app]
  erw [Category.id_comp]
  rw [← G.map_comp]
  have he := congrArg (fun k ↦ k.app n) (LR.evaluation.inv_hom_id_app X)
  simp only [NatTrans.comp_app, NatTrans.id_app] at he
  rw [he, G.map_id]
  erw [Category.comp_id]

private theorem strictTowerProductTransport
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasCountableProducts A] [HasCountableProducts B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    [HasCountableProducts (DerivedCategory.{w} B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) F)]
    [PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) F)]
    (LR : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q)
    (LS : StrictProjectionLimitData B DerivedCategory.Q DerivedCategory.Q)
    (e : (projectionPost F).mapDerivedCategory ⋙ LS.ev ≅
      LR.ev ⋙ projectionPost (I := ℕᵒᵖ) F.mapDerivedCategory)
    (he : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ),
      (LS.ev.map ((projectionPost F).mapDerivedCategoryFactors.hom.app X)).app n ≫
          (LS.evaluation.hom.app
            (((projectionPost F).mapHomologicalComplex (.up ℤ)).obj X)).app n ≫
          F.mapDerivedCategoryFactors.inv.app (X.asFunctor.obj n) =
        (e.hom.app (DerivedCategory.Q.obj X)).app n ≫
          F.mapDerivedCategory.map ((LR.evaluation.hom.app X).app n))
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    F.mapDerivedCategory.map (strictTowerResolvedProduct LR X) ≫
        piComparison F.mapDerivedCategory
          (fun n : ℕ ↦ (LR.ev.obj (DerivedCategory.Q.obj X)).obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ (e.inv.app (DerivedCategory.Q.obj X)).app (op n)) =
      F.mapDerivedCategoryFactors.hom.app (CoreWork.P.obj X) ≫
        DerivedCategory.Q.map (piComparison (F.mapHomologicalComplex (.up ℤ))
          (fun n : ℕ ↦ X.asFunctor.obj (op n))) ≫
        strictTowerResolvedProduct LS
          (((projectionPost F).mapHomologicalComplex (.up ℤ)).obj X) ≫
        Limits.Pi.map (fun n : ℕ ↦
          (LS.ev.map ((projectionPost F).mapDerivedCategoryFactors.inv.app X)).app (op n)) := by
  let G := F.mapDerivedCategory
  let Y := ((projectionPost F).mapHomologicalComplex (.up ℤ)).obj X
  have hi (n : ℕᵒᵖ) :
      G.map ((LR.evaluation.inv.app X).app n) ≫
          (e.inv.app (DerivedCategory.Q.obj X)).app n =
        F.mapDerivedCategoryFactors.hom.app (X.asFunctor.obj n) ≫
          (LS.evaluation.inv.app Y).app n ≫
          (LS.ev.map ((projectionPost F).mapDerivedCategoryFactors.inv.app X)).app n := by
    let ev := (evaluation ℕᵒᵖ (DerivedCategory.{w} B)).obj n
    let i₁ := ev.mapIso (LS.ev.mapIso
        ((projectionPost F).mapDerivedCategoryFactors.app X)) ≪≫
      ev.mapIso (LS.evaluation.app Y) ≪≫
        F.mapDerivedCategoryFactors.symm.app (X.asFunctor.obj n)
    let i₂ := ev.mapIso (e.app (DerivedCategory.Q.obj X)) ≪≫
      G.mapIso (((evaluation ℕᵒᵖ (DerivedCategory.{w} A)).obj n).mapIso
        (LR.evaluation.app X))
    have hh : i₁ = i₂ := Iso.ext (he X n)
    have hh' := congrArg Iso.inv hh
    dsimp only [i₁, i₂, ev, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv,
      Iso.app_inv, Functor.comp_map] at hh'
    simp only [Category.assoc] at hh'
    convert! hh'.symm using 1
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, Limits.Pi.map_π, piComparison_comp_π_assoc]
  dsimp only [strictTowerResolvedProduct]
  simp only [Category.assoc]
  rw [← F.mapDerivedCategory.map_comp_assoc]
  rw [Category.assoc]
  erw [Limits.Pi.map_π]
  simp only [F.mapDerivedCategory.map_comp, Category.assoc]
  erw [hi (op n)]
  rw [← F.mapDerivedCategory.map_comp_assoc, piComparison_comp_π]
  erw [F.mapDerivedCategoryFactors_hom_naturality_assoc]
  erw [Limits.Pi.map_π, Limits.Pi.map_π_assoc, piComparison_comp_π_assoc]
  rw [← DerivedCategory.Q.map_comp_assoc]
  erw [piComparison_comp_π]

private theorem strictTowerComparisonMap
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasCountableProducts A] [HasCountableProducts B]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    [HasCountableProducts (DerivedCategory.{w} B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) F)]
    [PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) F)]
    (LR : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q)
    (LS : StrictProjectionLimitData B DerivedCategory.Q DerivedCategory.Q)
    (ordinary : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ F ≅ projectionPost F ⋙ lim) :
    ∃ l : LR.L ⋙ F.mapDerivedCategory ⟶ (projectionPost F).mapDerivedCategory ⋙ LS.L,
      ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      F.mapDerivedCategory.map (LR.eta.app X) ≫ l.app (DerivedCategory.Q.obj X) =
        F.mapDerivedCategoryFactors.hom.app ((strictTowerLimitComplex A).obj X) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app X) ≫
        LS.eta.app (((projectionPost F).mapHomologicalComplex (.up ℤ)).obj X) ≫
        LS.L.map ((projectionPost F).mapDerivedCategoryFactors.inv.app X) := by
  let G := F.mapDerivedCategory
  let T := (projectionPost (I := ℕᵒᵖ) F).mapDerivedCategory
  let Fc := (projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)
  let ηG : strictTowerLimitComplex A ⋙ DerivedCategory.Q ⋙ G ⟶
      DerivedCategory.Q ⋙ LR.L ⋙ G :=
    Functor.whiskerRight LR.eta G ≫ (Functor.associator _ _ _).hom
  let : (LR.L ⋙ G).IsRightDerivedFunctor ηG
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) :=
    LocalizerMorphism.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure
      (CochainComplex.KInjectives.localizerMorphism (ℕᵒᵖ ⥤ A)) LR.eta
        (fun I ↦ LR.computes I.obj I.property) G
  let β : strictTowerLimitComplex A ⋙ DerivedCategory.Q ⋙ G ⟶
      DerivedCategory.Q ⋙ T ⋙ LS.L :=
    { app X := F.mapDerivedCategoryFactors.hom.app ((strictTowerLimitComplex A).obj X) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app X) ≫
        LS.eta.app (Fc.obj X) ≫
        LS.L.map ((projectionPost F).mapDerivedCategoryFactors.inv.app X)
      naturality X Y f := by
        dsimp only [Functor.comp_map]
        simp only [Category.assoc]
        erw [F.mapDerivedCategoryFactors.hom.naturality_assoc]
        dsimp only [Functor.comp_map]
        erw [← DerivedCategory.Q.map_comp_assoc]
        erw [(NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).naturality]
        rw [DerivedCategory.Q.map_comp, Category.assoc]
        have hn := LS.eta.naturality (Fc.map f)
        dsimp only [Functor.comp_map] at hn
        have he := congrArg (fun k ↦
          F.mapDerivedCategoryFactors.hom.app ((strictTowerLimitComplex A).obj X) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app X) ≫ k ≫
          LS.L.map ((projectionPost F).mapDerivedCategoryFactors.inv.app Y)) hn
        simp only [Category.assoc] at he
        refine he.trans ?_
        congr 3
        rw [← LS.L.map_comp]
        erw [(projectionPost F).mapDerivedCategoryFactors.inv.naturality]
        rw [LS.L.map_comp]
        rfl }
  refine ⟨(LR.L ⋙ G).rightDerivedDesc ηG
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) (T ⋙ LS.L) β, ?_⟩
  intro X
  simpa [ηG, β, G, T, Fc] using Functor.rightDerived_fac_app _ ηG
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) _ β X

private theorem exactFunctorBoundary
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (S : ShortComplex (CochainComplex A ℤ)) (hs : S.ShortExact) :
    F.mapDerivedCategory.map (DerivedCategory.triangleOfSESδ hs) ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj S.X₁) ≫
        (F.mapDerivedCategoryFactors.hom.app S.X₁)⟦(1 : ℤ)⟧' =
      F.mapDerivedCategoryFactors.hom.app S.X₃ ≫
        DerivedCategory.triangleOfSESδ
          (hs.map_of_exact (F.mapHomologicalComplex (.up ℤ))) := by
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let G := F.mapDerivedCategory
  let q := CochainComplex.mappingCone.descShortComplex S
  let d := (CochainComplex.mappingCone.triangle S.f).mor₃
  let c := (CochainComplex.mappingCone.mapHomologicalComplexIso S.f F).hom
  let hs' := hs.map_of_exact Fc
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hs
  have hc := NatTrans.shift_app_comm F.mapDerivedCategoryFactors.hom (1 : ℤ) S.X₁
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hc
  apply (cancel_epi (G.map (DerivedCategory.Q.map q))).mp
  dsimp only [G, q]
  rw [← F.mapDerivedCategory.map_comp_assoc,
    DerivedCategory.descShortComplex_triangleOfSESδ]
  simp only [Functor.map_comp, Category.assoc]
  rw [hc]
  erw [F.mapDerivedCategoryFactors.hom.naturality_assoc]
  dsimp only [Functor.comp_map]
  rw [← DerivedCategory.Q.map_comp_assoc]
  erw [CochainComplex.mappingCone.map_δ]
  rw [DerivedCategory.Q.map_comp, Category.assoc]
  erw [← DerivedCategory.descShortComplex_triangleOfSESδ hs']
  rw [← DerivedCategory.Q.map_comp_assoc]
  erw [CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex]
  simpa only [Category.assoc, Functor.comp_map] using
    (congrArg (fun k ↦ k ≫ DerivedCategory.triangleOfSESδ hs')
    (F.mapDerivedCategoryFactors.hom.naturality
      (CochainComplex.mappingCone.descShortComplex S))).symm

private theorem strictTowerResolvedProduct_natural
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    (L : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q)
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) :
    DerivedCategory.Q.map (CoreWork.P.map f) ≫ strictTowerResolvedProduct L Y =
      strictTowerResolvedProduct L X ≫
        Limits.Pi.map (fun n : ℕ ↦ (L.ev.map (DerivedCategory.Q.map f)).app (op n)) := by
  apply Pi.hom_ext
  intro n
  simp only [strictTowerResolvedProduct, Category.assoc, Limits.Pi.map_π_assoc,
    Limits.Pi.map_π, piComparison_comp_π_assoc]
  rw [← DerivedCategory.Q.map_comp_assoc, Limits.Pi.map_π,
    DerivedCategory.Q.map_comp, Category.assoc]
  congr 1
  exact congrArg (fun k ↦ k.app (op n)) (L.evaluation.inv.naturality f)

private theorem strictTowerBoundaryOfShortExact
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    (L : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q)
    (hn : strictTowerRoosNormalized L)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (hs : (CoreWork.S X).ShortExact) :
    strictTowerResolvedProduct L X ≫ L.delta (DerivedCategory.Q.obj X) =
      DerivedCategory.triangleOfSESδ hs ≫ (L.eta.app X)⟦(1 : ℤ)⟧' := by
  let I := (CoreWork.F (A := A)).obj X
  let q := (CoreWork.q (A := A)).app X
  have hi : I.IsKInjective := inferInstance
  have hinj (k : ℤ) : Injective (I.X k) := inferInstance
  have hI := CoreWork.hS I
  have hnI := hn.2 I hi hinj (CoreWork.S I).zero hI
  have hnat := DerivedCategory.triangleOfSESδ_naturality hs hI (CoreWork.Smap q)
  have hη := L.eta.naturality q
  dsimp only [Functor.comp_map] at hη
  have := CoreWork.q_quasiIso X
  apply (cancel_mono ((L.L.map (DerivedCategory.Q.map q))⟦(1 : ℤ)⟧')).mp
  rw [Category.assoc, ← L.delta_natural, ← Category.assoc]
  erw [← strictTowerResolvedProduct_natural L q]
  rw [Category.assoc, hnI]
  simp only [Category.assoc]
  rw [← Functor.map_comp]
  have he := congrArg (fun k ↦
    DerivedCategory.triangleOfSESδ hs ≫ k⟦(1 : ℤ)⟧') hη
  have he' := congrArg (fun k ↦ k ≫ (L.eta.app I)⟦(1 : ℤ)⟧') hnat.symm
  simp only [Category.assoc] at he'
  simp only [Functor.map_comp] at he
  refine he'.trans ?_
  simp only [Functor.map_comp] at he ⊢
  convert! he using 1

private theorem ordinaryTowerComparison_inclusion
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfSize.{0, 0} F]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (NatTrans.mapHomologicalComplex (preservesLimitNatIso F).hom (.up ℤ)).app X ≫
        strictTowerLimitInclusion
          (((projectionPost F).mapHomologicalComplex (.up ℤ)).obj X) =
      (F.mapHomologicalComplex (.up ℤ)).map (strictTowerLimitInclusion X) ≫
        piComparison (F.mapHomologicalComplex (.up ℤ))
          (fun n : ℕ ↦ X.asFunctor.obj (op n)) := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, strictTowerLimitInclusion, Limits.Pi.lift_comp_π, Category.assoc]
  erw [piComparison_comp_π]
  rw [← Functor.map_comp, strictTowerLimitInclusion, Limits.Pi.lift_comp_π]
  ext k
  exact preservesLimitIso_hom_π F (X.X k) (op n)

private theorem exactFunctorRoosShortComplex
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfSize.{0, 0} F]
    [PreservesFiniteColimits F] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ∃ m : (CoreWork.S X).map (F.mapHomologicalComplex (.up ℤ)) ⟶
        CoreWork.S (((projectionPost F).mapHomologicalComplex (.up ℤ)).obj X),
      m.τ₁ = (NatTrans.mapHomologicalComplex (preservesLimitNatIso F).hom (.up ℤ)).app X ∧
      m.τ₂ = piComparison (F.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ X.asFunctor.obj (op n)) ∧ m.τ₃ = m.τ₂ ∧ IsIso m := by
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let : HasCountableProducts (CochainComplex A ℤ) := ⟨fun K ↦ inferInstance⟩
  let : HasCountableProducts (CochainComplex B ℤ) := ⟨fun K ↦ inferInstance⟩
  let Y := ((projectionPost F).mapHomologicalComplex (.up ℤ)).obj X
  let b := (NatTrans.mapHomologicalComplex (preservesLimitNatIso F).hom (.up ℤ)).app X
  let c := piComparison Fc (fun n : ℕ ↦ X.asFunctor.obj (op n))
  let m : (CoreWork.S X).map Fc ⟶ CoreWork.S Y :=
    { τ₁ := b
      τ₂ := c
      τ₃ := c
      comm₁₂ := ordinaryTowerComparison_inclusion F X
      comm₂₃ := by
        symm
        have h :=
          towerProductComparison_middle Fc X.asFunctor Y.asFunctor (Iso.refl _)
        dsimp only [Iso.refl_hom, NatTrans.id_app] at h
        erw [Limits.Pi.map_id, Category.id_comp, Category.comp_id] at h
        exact h }
  refine ⟨m, rfl, rfl, rfl, ?_⟩
  let : IsIso m.τ₁ := by
    exact inferInstanceAs (IsIso
      ((NatIso.mapHomologicalComplex (preservesLimitNatIso F) (.up ℤ)).app X).hom)
  let : IsIso m.τ₂ := by dsimp only [m]; infer_instance
  let : IsIso m.τ₃ := by dsimp only [m]; infer_instance
  exact ShortComplex.isIso_of_isIso m

private theorem towerNaturalTransformations
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    (L : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q) :
    ∃ (p : L.L ⟶ L.ev ⋙ CoreWork.DP)
      (d : L.ev ⋙ CoreWork.DP ⟶ L.L ⋙ shiftFunctor _ (1 : ℤ)),
      (∀ Z, p.app Z = L.p Z) ∧ (∀ Z, d.app Z = L.delta Z) := by
  exact ⟨⟨L.p, fun _ _ f ↦ L.p_natural f⟩,
    ⟨L.delta, fun _ _ f ↦ L.delta_natural f⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

private theorem naturalTransformations_eq_of_kInjectives
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{r} A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B]
    {F G : DerivedCategory.{w} A ⥤ B} (α β : F ⟶ G)
    (h : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      (∀ k : ℤ, Injective (I.X k)) →
      α.app (DerivedCategory.Q.obj I) = β.app (DerivedCategory.Q.obj I)) : α = β := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
  intro X
  let I := (CochainComplex.kInjectiveResolutionFunctor.{r} A).obj X
  let q := (CochainComplex.toKInjectiveResolution.{r} A).app X
  have : QuasiIso q := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app A X).2
  have : I.IsKInjective := inferInstance
  have hinj (k : ℤ) : Injective (I.X k) := inferInstance
  apply (cancel_mono (G.map (DerivedCategory.Q.map q))).mp
  rw [← α.naturality, ← β.naturality, h I inferInstance hinj]

private theorem derivedTowerProductComparison
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    [HasCountableProducts (DerivedCategory.{w} B)]
    (G : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
    (T : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ B))
    (LR : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q)
    (LS : StrictProjectionLimitData B DerivedCategory.Q DerivedCategory.Q)
    (e : T ⋙ LS.ev ≅ LR.ev ⋙ projectionPost (I := ℕᵒᵖ) G) :
    ∃ c : LR.ev ⋙ CoreWork.DP ⋙ G ⟶ T ⋙ LS.ev ⋙ CoreWork.DP,
      ∀ Z, c.app Z = piComparison G
        (fun n : ℕ ↦ (LR.ev.obj Z).obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ (e.inv.app Z).app (op n)) := by
  refine ⟨
    { app Z := piComparison G _ ≫
        Limits.Pi.map (fun n : ℕ ↦ (e.inv.app Z).app (op n))
      naturality X Y f := ?_ }, fun _ ↦ rfl⟩
  apply Pi.hom_ext
  intro n
  dsimp only [Functor.comp_map, CoreWork.DP]
  simp only [Category.assoc, Limits.Pi.map_π, piComparison_comp_π_assoc]
  rw [← G.map_comp_assoc, Limits.Pi.map_π, G.map_comp, Category.assoc]
  erw [Limits.Pi.map_π_assoc, piComparison_comp_π_assoc]
  congr 1
  exact congrArg (fun k ↦ k.app (op n)) (e.inv.naturality f)

private theorem strictTowerTransport
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasCountableProducts A] [HasCountableProducts B]
    [IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A)]
    [IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    [HasCountableProducts (DerivedCategory.{w} B)]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfSize.{0, 0} F]
    [PreservesFiniteColimits F]
    [PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) F)]
    [PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) F)]
    (LR : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q)
    (LS : StrictProjectionLimitData B DerivedCategory.Q DerivedCategory.Q)
    (hLR : ∃ (_ : LR.L.CommShift ℤ), LR.L.IsTriangulated)
    (hLS : ∃ (_ : LS.L.CommShift ℤ), LS.L.IsTriangulated)
    (hnR : strictTowerRoosNormalized LR) (hnS : strictTowerRoosNormalized LS)
    (hp : ∀ M : ℕ → DerivedCategory.{w} A, IsIso (piComparison F.mapDerivedCategory M)) :
    Nonempty (FiniteFreeStrictTowerTransport F F.mapDerivedCategory
      (projectionPost F).mapDerivedCategory F.mapDerivedCategoryFactors
      (projectionPost F).mapDerivedCategoryFactors) := by
  let G := F.mapDerivedCategory
  let T := (projectionPost (I := ℕᵒᵖ) F).mapDerivedCategory
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Ft := (projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)
  let ordinary := preservesLimitNatIso (J := ℕᵒᵖ) F
  obtain ⟨e, he⟩ := strictTowerEvaluationIso F LR LS
  obtain ⟨l, hl⟩ := strictTowerComparisonMap F LR LS ordinary
  obtain ⟨c, hc⟩ := derivedTowerProductComparison G T LR LS e
  obtain ⟨pR, dR, hpR, hdR⟩ := towerNaturalTransformations LR
  obtain ⟨pS, dS, hpS, hdS⟩ := towerNaturalTransformations LS
  let α := Functor.whiskerRight pR G ≫ c
  let β := l ≫ Functor.whiskerLeft T pS
  have hf : α = β := by
    apply naturalTransformations_eq_of_kInjectives α β
    intro I hI hinj
    have := LR.computes I hI
    apply (cancel_epi (G.map (LR.eta.app I))).mp
    dsimp only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    rw [hpR, hpS, ← G.map_comp_assoc, hnR.1 I, G.map_comp, Category.assoc, hc]
    erw [strictTowerProductTransport F LR LS e he I]
    erw [F.mapDerivedCategoryFactors_hom_naturality_assoc]
    dsimp only [Functor.comp_map]
    rw [← DerivedCategory.Q.map_comp_assoc,
      ← ordinaryTowerComparison_inclusion F I, DerivedCategory.Q.map_comp]
    simp only [Category.assoc]
    rw [← reassoc_of% (hnS.1 (Ft.obj I)), ← LS.p_natural]
    erw [reassoc_of% (hl I)]
    rfl
  have hfirst (Z : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) :
      G.map (LR.p Z) ≫ c.app Z = l.app Z ≫ LS.p (T.obj Z) := by
    simpa only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, hpR, hpS] using congr_app hf Z
  let αδ : LR.ev ⋙ CoreWork.DP ⋙ G ⟶
      T ⋙ LS.L ⋙ shiftFunctor _ (1 : ℤ) :=
    Functor.whiskerRight dR G ≫
      Functor.whiskerLeft LR.L (G.commShiftIso (1 : ℤ)).hom ≫
      Functor.whiskerRight l (shiftFunctor _ (1 : ℤ))
  let βδ := c ≫ Functor.whiskerLeft T dS
  have hd : αδ = βδ := by
    apply naturalTransformations_eq_of_kInjectives αδ βδ
    intro I hI hinj
    let : I.IsKInjective := hI
    let k : ∀ n : ℤ, Injective (I.X n) := hinj
    have hr : IsIso (strictTowerResolvedProduct LR I) := by
      dsimp only [strictTowerResolvedProduct]
      have := CoreWork.pc_isIso I
      infer_instance
    have hs := CoreWork.hS I
    obtain ⟨m, hm₁, hm₂, hm₃, hm⟩ := exactFunctorRoosShortComplex F I
    let := hm
    let hsF := hs.map_of_exact Fc
    have hsY : (CoreWork.S (Ft.obj I)).ShortExact :=
      ShortComplex.shortExact_of_iso (asIso m) hsF
    have hδ := DerivedCategory.triangleOfSESδ_naturality hsF hsY m
    rw [hm₁, hm₃, hm₂] at hδ
    have hb := exactFunctorBoundary F (CoreWork.S I) hs
    have hnI := hnR.2 I hI hinj (CoreWork.S I).zero hs
    have hnY := strictTowerBoundaryOfShortExact LS hnS (Ft.obj I) hsY
    dsimp only [αδ, βδ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    rw [hdR, hdS]
    apply (cancel_epi (G.map (strictTowerResolvedProduct LR I))).mp
    rw [← G.map_comp_assoc, hnI, G.map_comp, Category.assoc]
    erw [G.commShiftIso_hom_naturality_assoc]
    rw [← Functor.map_comp]
    erw [hl I]
    simp only [Functor.map_comp]
    rw [reassoc_of% hb]
    rw [reassoc_of% hδ]
    rw [hc]
    simp only [Category.assoc]
    erw [reassoc_of% (strictTowerProductTransport F LR LS e he I)]
    erw [LS.delta_natural]
    rw [reassoc_of% hnY]
  have hlast (Z : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) :
      G.map (LR.delta Z) ≫ (G.commShiftIso (1 : ℤ)).hom.app (LR.L.obj Z) ≫
          (l.app Z)⟦(1 : ℤ)⟧' = c.app Z ≫ LS.delta (T.obj Z) := by
    simpa only [αδ, βδ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, hdR, hdS, Category.assoc] using congr_app hd Z
  have hmiddle (Z : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) :
      G.map (towerTransitionEndomorphism
        (fun n : ℕ ↦ (LR.ev.obj Z).map (homOfLE (Nat.le_succ n)).op)) ≫ c.app Z =
      c.app Z ≫ towerTransitionEndomorphism
        (fun n : ℕ ↦ (LS.ev.obj (T.obj Z)).map (homOfLE (Nat.le_succ n)).op) := by
    rw [hc]
    simpa only [Iso.app_hom, Iso.symm_hom, Category.assoc] using
      towerProductComparison_middle G (LR.ev.obj Z) (LS.ev.obj (T.obj Z)) (e.symm.app Z)
  have hiapp (Z : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) : IsIso (l.app Z) := by
    let m : G.mapTriangle.obj (Triangle.mk (LR.p Z)
        (towerTransitionEndomorphism
          (fun n : ℕ ↦ (LR.ev.obj Z).map (homOfLE (Nat.le_succ n)).op)) (LR.delta Z)) ⟶
        Triangle.mk (LS.p (T.obj Z)) (towerTransitionEndomorphism
          (fun n : ℕ ↦ (LS.ev.obj (T.obj Z)).map (homOfLE (Nat.le_succ n)).op))
          (LS.delta (T.obj Z)) :=
      { hom₁ := l.app Z
        hom₂ := c.app Z
        hom₃ := c.app Z
        comm₁ := hfirst Z
        comm₂ := hmiddle Z
        comm₃ := by
          dsimp only [Functor.mapTriangle, Triangle.mk]
          simpa only [Category.assoc] using hlast Z }
    have : IsIso (c.app Z) := by
      rw [hc]
      let := hp (fun n ↦ (LR.ev.obj Z).obj (op n))
      infer_instance
    exact isIso₁_of_isIso₂₃ m (G.map_distinguished _ (LR.roos Z))
      (LS.roos (T.obj Z)) inferInstance inferInstance
  let : ∀ Z, IsIso (l.app Z) := hiapp
  let : IsIso l := NatIso.isIso_of_isIso_app l
  let comparison := asIso l
  refine ⟨{ source := LR
            target := LS
            source_exact := hLR
            target_exact := hLS
            source_normalized := hnR
            target_normalized := hnS
            ordinary := ordinary
            ordinary_normalized := fun _ ↦ rfl
            products := hp
            evaluation := e
            evaluation_normalized := he
            comparison := comparison
            comparison_normalized := hl
            roos_first := ?_
            roos_middle := ?_
            roos_last := ?_
            augmentation := ?_
            augmented_naturality := ?_ }⟩
  · intro Z
    simpa only [comparison, asIso_hom, hc, Category.assoc] using hfirst Z
  · intro Z
    simpa only [hc, Category.assoc] using hmiddle Z
  · intro Z
    simpa only [comparison, asIso_hom, hc, Category.assoc] using hlast Z
  · intro M X z
    change G.map _ ≫ l.app _ = _
    rw [Functor.map_comp, Category.assoc, hl X]
    erw [F.mapDerivedCategoryFactors_hom_naturality_assoc]
    rw [← DerivedCategory.Q.map_comp_assoc]
  · intro M N X Y z t h v hv
    change G.map _ ≫ l.app _ ≫ LS.L.map (T.map _) = G.map _ ≫ G.map _ ≫ l.app _
    have hlv := l.naturality (DerivedCategory.Q.map v)
    dsimp only [Functor.comp_map] at hlv
    rw [← hlv, ← G.map_comp_assoc]
    have hz : (DerivedCategory.Q.map z ≫ LR.eta.app X) ≫
        LR.L.map (DerivedCategory.Q.map v) =
      DerivedCategory.Q.map h ≫ (DerivedCategory.Q.map t ≫ LR.eta.app Y) := by
      rw [Category.assoc]
      erw [← LR.eta.naturality]
      dsimp only [Functor.comp_map]
      rw [← Category.assoc, ← DerivedCategory.Q.map_comp, hv,
        DerivedCategory.Q.map_comp, Category.assoc]
    rw [hz, G.map_comp, Category.assoc]

private theorem strictTowerNormalizedData
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [HasCountableProducts (DerivedCategory.{w} A)] :
    ∃ L : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q,
      (∃ (_ : L.L.CommShift ℤ), L.L.IsTriangulated) ∧ strictTowerRoosNormalized L := by
  classical
  let : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive := by
    constructor
    intro X Y f g
    apply limit.hom_ext
    intro n
    simp only [lim_map, limMap_π, Preadditive.add_comp, NatTrans.app_add,
      Preadditive.comp_add]
  obtain ⟨RF, η, hRF, hI, hshift, hTri⟩ := totalDerivedData
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A)
  obtain ⟨E, ⟨ε⟩⟩ := evaluationData (A := A)
  let L : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q :=
    { L := RF
      eta := η
      ev := E
      evaluation := ε
      p := (CoreWork.pNat RF η hI E ε).app
      delta := (CoreWork.deltaNat RF η hI E ε).app
      derived := hRF
      computes := hI
      roos := by
        intro Z
        let X := DerivedCategory.Q.objPreimage Z
        let e := DerivedCategory.Q.objObjPreimageIso Z
        have h := CoreWork.roos_Q RF η hI E ε X
        exact CategoryTheory.Pretriangulated.isomorphic_distinguished _ h _
          (Triangle.isoMk _ _ (RF.mapIso e) ((E ⋙ CoreWork.DP).mapIso e)
            ((E ⋙ CoreWork.DP).mapIso e)
            ((CoreWork.pNat RF η hI E ε).naturality e.hom).symm
            ((CoreWork.dDP).naturality (E.map e.hom)).symm
            ((CoreWork.deltaNat RF η hI E ε).naturality e.hom).symm).symm
      p_natural := fun v ↦ (CoreWork.pNat RF η hI E ε).naturality v
      delta_natural := fun v ↦ (CoreWork.deltaNat RF η hI E ε).naturality v }
  have ha (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      DerivedCategory.Q.map (CoreWork.L.map (CoreWork.q.app X)) ≫
          (CoreWork.aIso RF η hI).hom.app X = η.app X := by
    have : QuasiIso (CoreWork.q.app X) := CoreWork.q_quasiIso X
    have : IsIso (η.app (CoreWork.F.obj X)) := hI _ inferInstance
    dsimp only [CoreWork.aIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, asIso_hom, asIso_inv,
      Functor.comp_obj, Category.id_comp, Category.comp_id]
    simp only [Category.id_comp, NatIso.isIso_inv_app, Functor.whiskerRight_app]
    change DerivedCategory.Q.map (CoreWork.L.map (CoreWork.q.app X)) ≫
      η.app (CoreWork.F.obj X) ≫ RF.map (inv (DerivedCategory.Q.map
        (CoreWork.q.app X))) = _
    erw [η.naturality_assoc]
    simp
  have hb (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      DerivedCategory.Q.map (CoreWork.P.map (CoreWork.q.app X)) ≫
          (CoreWork.bIso E ε).hom.app X = strictTowerResolvedProduct L X := by
    have : QuasiIso (CoreWork.q.app X) := CoreWork.q_quasiIso X
    have : ∀ n : ℕᵒᵖ,
        IsIso ((CoreWork.evQ.map (CoreWork.q.app X)).app n) := by
      intro n
      change IsIso (DerivedCategory.Q.map
        ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).map
          (CoreWork.q.app X)))
      infer_instance
    have : IsIso (CoreWork.evQ.map (CoreWork.q.app X)) := NatIso.isIso_of_isIso_app _
    have hqapp (Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
        IsIso ((Functor.whiskerRight (CoreWork.q (A := A)) CoreWork.evQ).app Y) := by
      have : QuasiIso (CoreWork.q.app Y) := CoreWork.q_quasiIso Y
      change IsIso (CoreWork.evQ.map (CoreWork.q.app Y))
      have (n : ℕᵒᵖ) : IsIso ((CoreWork.evQ.map (CoreWork.q.app Y)).app n) := by
        change IsIso (DerivedCategory.Q.map
          ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).map
            (CoreWork.q.app Y)))
        infer_instance
      exact NatIso.isIso_of_isIso_app _
    have hq : IsIso (Functor.whiskerRight (CoreWork.q (A := A)) CoreWork.evQ) :=
      NatIso.isIso_of_isIso_app _
    let c := (asIso (Functor.whiskerRight (CoreWork.q (A := A)) CoreWork.evQ)).symm ≪≫
      ε.symm
    have hc : (CoreWork.bIso E ε).hom.app X =
        CoreWork.pc.app (CoreWork.F.obj X) ≫ CoreWork.DP.map (c.hom.app X) := by
      simp only [CoreWork.bIso, Iso.trans_hom, Iso.symm_hom,
        Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, asIso_hom, Functor.associator,
        Category.id_comp, Category.comp_id, c]
    rw [hc, ← Category.assoc]
    have hn := (CoreWork.pc (A := A)).naturality (CoreWork.q.app X)
    change DerivedCategory.Q.map (CoreWork.P.map (CoreWork.q.app X)) ≫
      CoreWork.pc.app (CoreWork.F.obj X) =
      CoreWork.pc.app X ≫ CoreWork.DP.map (CoreWork.evQ.map (CoreWork.q.app X)) at hn
    rw [hn, Category.assoc, ← Functor.map_comp]
    have hh : CoreWork.evQ.map (CoreWork.q.app X) ≫ c.hom.app X = ε.inv.app X := by
      simp [c, NatIso.isIso_inv_app]
    rw [hh]
    rfl
  refine ⟨L, ⟨hshift, hTri⟩, ?_, ?_⟩
  · intro X
    change η.app X ≫ (CoreWork.pNat RF η hI E ε).app _ = _
    rw [CoreWork.pNat_app]
    change η.app X ≫ (CoreWork.aIso RF η hI).inv.app X ≫
      DerivedCategory.Q.map (CoreWork.inc.app (CoreWork.F.obj X)) ≫
      (CoreWork.bIso E ε).hom.app X = _
    rw [← ha X]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← DerivedCategory.Q.map_comp_assoc]
    erw [CoreWork.inc.naturality]
    rw [DerivedCategory.Q.map_comp, Category.assoc, hb X]
    rfl
  · intro I hkinj hinj h hs
    change strictTowerResolvedProduct L I ≫
      (CoreWork.deltaNat RF η hI E ε).app _ = _
    rw [CoreWork.deltaNat_app]
    rw [← hb I]
    simp only [CoreWork.deltaPre, NatTrans.comp_app, Functor.whiskerRight_app,
      Category.assoc]
    change DerivedCategory.Q.map (CoreWork.P.map (CoreWork.q.app I)) ≫
      (CoreWork.bIso E ε).hom.app I ≫ (CoreWork.bIso E ε).inv.app I ≫
      DerivedCategory.triangleOfSESδ (CoreWork.hS (CoreWork.F.obj I)) ≫
      ((CoreWork.aIso RF η hI).hom.app I)⟦(1 : ℤ)⟧' = _
    simp only [Iso.hom_inv_id_app_assoc]
    have hn := DerivedCategory.triangleOfSESδ_naturality hs
      (CoreWork.hS (CoreWork.F.obj I)) (CoreWork.Smap (CoreWork.q.app I))
    change DerivedCategory.triangleOfSESδ hs ≫
      (DerivedCategory.Q.map (CoreWork.L.map (CoreWork.q.app I)))⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map (CoreWork.P.map (CoreWork.q.app I)) ≫
        DerivedCategory.triangleOfSESδ (CoreWork.hS (CoreWork.F.obj I)) at hn
    have hn' := congrArg (· ≫
      ((CoreWork.aIso RF η hI).hom.app I)⟦(1 : ℤ)⟧') hn.symm
    calc
      _ = _ := by simpa only [Category.assoc] using hn'
      _ = _ := by rw [← Functor.map_comp, ha I]

end CategoryTheory

namespace SheafOfModules

open CategoryTheory.MonoidalCategory

open CategoryTheory.MonoidalCategory in
private noncomputable def tensorFreePowerIso
    {H : Type uA} [Category.{vA} H] [Abelian H] [MonoidalCategory H]
    [MonoidalPreadditive H] (R : H) (I : Type) [Finite I]
    (e : R ≅ 𝟙_ H) :
    tensorLeft (∐ (fun _ : I ↦ R)) ≅ Functor.const (Discrete I) ⋙ lim := by
  classical
  let : HasFiniteBiproducts H := HasFiniteBiproducts.of_hasFiniteProducts
  let i (M : H) : (∐ (fun _ : I ↦ R)) ⊗ M ≅ ∏ᶜ (fun _ : I ↦ M) :=
    (tensorRight M).mapIso (biproduct.isoCoproduct (fun _ : I ↦ R)).symm ≪≫
      (tensorRight M).mapBiproduct (fun _ : I ↦ R) ≪≫
      biproduct.mapIso (fun _ : I ↦ whiskerRightIso e M ≪≫ λ_ M) ≪≫
      biproduct.isoProduct _
  have hi (M : H) (j : I) : (i M).hom ≫ Pi.π _ j =
      ((biproduct.isoCoproduct (fun _ : I ↦ R)).inv ≫
        biproduct.π _ j ≫ e.hom) ▷ M ≫ (λ_ M).hom := by
    simp only [i, Iso.trans_hom, Category.assoc, biproduct.isoProduct_hom,
      Pi.lift_comp_π, biproduct.mapIso_hom, biproduct.map_π, Functor.mapBiproduct_hom,
      Functor.mapIso_hom, Iso.symm_hom, whiskerRightIso_hom,
      comp_whiskerRight]
    erw [biproduct.lift_π_assoc]
    rfl
  refine NatIso.ofComponents i ?_
  intro M N f
  change (∐ (fun _ : I ↦ R)) ◁ f ≫ (i N).hom =
    (i M).hom ≫ Limits.Pi.map (fun _ : I ↦ f)
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, hi, Limits.Pi.map_π]
  rw [whisker_exchange_assoc, leftUnitor_naturality]
  simpa only [Category.assoc] using congrArg (· ≫ f) (hi M j).symm

private theorem restrictedScalarTensorIso
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {O S : Sheaf J CommRingCat.{r}} (a : O ⟶ S)
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, w, w} a) :
    Nonempty (D.E ⋙ restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ≅
      MonoidalCategory.tensorLeft
        ((restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (unit (derivedChangeRingIndependentCoefficients J S)))) := by
  let U := restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)
  let N := U.obj (unit (derivedChangeRingIndependentCoefficients J S))
  obtain ⟨e, he⟩ := exists_changeOfRings_tensorCancellation_independentCoefficients a
  let i (M) : U.obj (D.E.obj M) ≅ N ⊗ M :=
    U.mapIso (eqToIso (D.obj_eq M)) ≪≫
      U.mapIso (MonoidalCategory.leftUnitor (changeOfRings a M)).symm ≪≫
      e (unit (derivedChangeRingIndependentCoefficients J S)) M
  refine ⟨NatIso.ofComponents i ?_⟩
  intro M M' f
  dsimp only [i, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.comp_map, MonoidalCategory.tensorLeft]
  rw [D.map_eq]
  dsimp only [U]
  simp only [Functor.map_comp, eqToIso.hom, Category.assoc]
  simp only [← Functor.map_comp_assoc]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Functor.map_comp,
    Category.assoc]
  have hn := congrArg U.map
    ((MonoidalCategory.leftUnitorNatIso _).inv.naturality (changeOfRingsHom a M f))
  simp only [Functor.map_comp] at hn
  change U.map (changeOfRingsHom a M f) ≫ U.map (λ_ _).inv =
    U.map (λ_ _).inv ≫ U.map (_ ◁ changeOfRingsHom a M f) at hn
  rw [reassoc_of% hn]
  have hc : U.map (𝟙_ _ ◁ changeOfRingsHom a M f) ≫
      (e (unit (derivedChangeRingIndependentCoefficients J S)) M').hom =
      (e (unit (derivedChangeRingIndependentCoefficients J S)) M).hom ≫
        (tensorLeft N).map f := by
    have hc := he (𝟙 (unit (derivedChangeRingIndependentCoefficients J S))) f
    change U.map (_ ⊗ₘ changeOfRingsHom a M f) ≫ _ =
      _ ≫ (U.map (𝟙 _) ⊗ₘ f) at hc
    rw [U.map_id, id_tensorHom, id_tensorHom] at hc
    exact hc
  rw [hc]

private theorem scalarRestrictionProperties
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J RingCat.{r}} (a : R ⟶ S) :
    (restrictScalars.{r} a).ReflectsIsomorphisms ∧
      PreservesLimitsOfSize.{r, r} (restrictScalars.{r} a) ∧
      PreservesColimitsOfSize.{r, r} (restrictScalars.{r} a) := by
  have hlim (A : Sheaf J RingCat.{r}) :
      PreservesLimitsOfSize.{r, r} (toSheaf.{r} A) :=
    by
      constructor
      intro K _
      exact ((CategoryTheory.moduleSheaves_colimits_forgetful A).2.2.2.2.2 K).1
  have hcolim (A : Sheaf J RingCat.{r}) :
      PreservesColimitsOfSize.{r, r} (toSheaf.{r} A) :=
    by
      constructor
      intro K _
      exact ((CategoryTheory.moduleSheaves_colimits_forgetful A).2.2.2.2.2 K).2.1
  let : PreservesLimitsOfSize.{r, r} (toSheaf.{r} R) := hlim R
  let : PreservesLimitsOfSize.{r, r} (toSheaf.{r} S) := hlim S
  let : PreservesColimitsOfSize.{r, r} (toSheaf.{r} R) := hcolim R
  let : PreservesColimitsOfSize.{r, r} (toSheaf.{r} S) := hcolim S
  let : ReflectsLimitsOfSize.{r, r} (toSheaf.{r} R) :=
    reflectsLimits_of_reflectsIsomorphisms
  let : ReflectsColimitsOfSize.{r, r} (toSheaf.{r} R) :=
    reflectsColimits_of_reflectsIsomorphisms
  let : PreservesLimitsOfSize.{r, r} (restrictScalars a ⋙ toSheaf.{r} R) :=
    inferInstanceAs (PreservesLimitsOfSize.{r, r} (toSheaf.{r} S))
  let : PreservesColimitsOfSize.{r, r} (restrictScalars a ⋙ toSheaf.{r} R) :=
    inferInstanceAs (PreservesColimitsOfSize.{r, r} (toSheaf.{r} S))
  refine ⟨⟨?_⟩, preservesLimits_of_reflects_of_preserves _ (toSheaf.{r} R),
    preservesColimits_of_reflects_of_preserves _ (toSheaf.{r} R)⟩
  intro M N f hf
  have : IsIso ((toSheaf.{r} S).map f) :=
    inferInstanceAs (IsIso ((toSheaf.{r} R).map ((restrictScalars a).map f)))
  exact isIso_of_reflects_iso f (toSheaf.{r} S)

private theorem scalarFiniteCoordinates
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {O S : Sheaf J CommRingCat.{r}} (a : O ⟶ S)
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, w, w} a)
    (hfree : ∃ d : ℕ, Nonempty
      (free (R := derivedChangeRingIndependentCoefficients J O) (ULift.{r} (Fin d)) ≅
        (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (unit (derivedChangeRingIndependentCoefficients J S)))) :
    ∃ d : ℕ, Nonempty
      (D.E ⋙ restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ≅
        Functor.const (Discrete (Fin d)) ⋙ lim) := by
  classical
  obtain ⟨d, ⟨e⟩⟩ := hfree
  obtain ⟨i⟩ := restrictedScalarTensorIso a D
  have (I : Type r) : HasColimitsOfShape (Discrete I) (PresheafOfModules.{r}
      (derivedChangeRingIndependentCoefficients J O).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  let j := e.symm ≪≫ Sigma.reindex (Equiv.ulift : ULift.{r} (Fin d) ≃ Fin d)
    (fun _ ↦ unit (derivedChangeRingIndependentCoefficients J O))
  exact ⟨d, ⟨i ≪≫ (tensoringLeft _).mapIso j ≪≫
    tensorFreePowerIso _ (Fin d) (Iso.refl _)⟩⟩

private theorem scalarFiniteExact
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {O S : Sheaf J CommRingCat.{r}} (a : O ⟶ S)
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, w, w} a)
    (hfree : ∃ d : ℕ, Nonempty
      (free (R := derivedChangeRingIndependentCoefficients J O) (ULift.{r} (Fin d)) ≅
        (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (unit (derivedChangeRingIndependentCoefficients J S)))) :
    PreservesLimitsOfSize.{0, 0} D.E ∧ PreservesFiniteColimits D.E := by
  classical
  let U := restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)
  obtain ⟨href, hlim, hcolim⟩ := scalarRestrictionProperties
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)
  let : U.ReflectsIsomorphisms := href
  let : PreservesLimitsOfSize.{r, r} U := hlim
  let : PreservesColimitsOfSize.{r, r} U := hcolim
  let : HasLimitsOfSize.{r, r} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S)) :=
    (moduleSheaves_colimits_forgetful
      (derivedChangeRingIndependentCoefficients J S)).2.2.2.1
  let : HasColimitsOfSize.{r, r} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S)) :=
    (moduleSheaves_colimits_forgetful
      (derivedChangeRingIndependentCoefficients J S)).2.2.2.2.1
  let : HasLimitsOfSize.{0, 0} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S)) := hasLimitsOfSizeShrink _
  let : HasColimitsOfSize.{0, 0} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S)) := hasColimitsOfSizeShrink _
  let : PreservesLimitsOfSize.{0, 0} U := preservesLimitsOfSize_shrink _
  let : PreservesColimitsOfSize.{0, 0} U := preservesColimitsOfSize_shrink _
  let : ReflectsLimitsOfSize.{0, 0} U := reflectsLimits_of_reflectsIsomorphisms
  let : ReflectsFiniteColimits U := inferInstance
  obtain ⟨d, ⟨e⟩⟩ := scalarFiniteCoordinates a D hfree
  let : HasFiniteBiproducts (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J O)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let P := (Functor.const (Discrete (Fin d)) : ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J O) ⥤ _) ⋙ lim
  let : PreservesLimitsOfSize.{0, 0} P := inferInstance
  let : PreservesFiniteColimits P := by
    have (I : Type r) : HasColimitsOfShape (Discrete I) (PresheafOfModules.{r}
        (derivedChangeRingIndependentCoefficients J O).obj) :=
      PresheafOfModules.hasColimitsOfShape _ _
    let : PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
        (colim : (Discrete (Fin d) ⥤ ringedSiteModules.{r}
          (derivedChangeRingIndependentCoefficients J O)) ⥤ _)) := inferInstance
    exact preservesFiniteColimits_of_natIso
      (Functor.isoWhiskerLeft _ HasBiproductsOfShape.colimIsoLim)
  let : PreservesLimitsOfSize.{0, 0} (D.E ⋙ U) := preservesLimits_of_natIso e.symm
  let : PreservesFiniteColimits (D.E ⋙ U) := preservesFiniteColimits_of_natIso e.symm
  exact ⟨preservesLimits_of_reflects_of_preserves D.E U,
    preservesFiniteColimits_of_reflects_of_preserves D.E U⟩

private theorem scalarExactDerivedIso
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {O S : Sheaf J CommRingCat.{r}} (a : O ⟶ S)
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, w, w} a) [PreservesFiniteLimits D.E]
    [PreservesFiniteColimits D.E] :
    ∃ κ : D.T ≅ D.E.mapDerivedCategory,
      ∀ M, D.ε.app M = κ.hom.app (DerivedCategory.Q.obj M) ≫
        D.E.mapDerivedCategoryFactors.hom.app M := by
  let W := HomologicalComplex.quasiIso
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O)) (.up ℤ)
  let : D.T.IsLeftDerivedFunctor D.ε W := D.universal
  let : D.E.mapDerivedCategory.IsLeftDerivedFunctor
      D.E.mapDerivedCategoryFactors.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ D.E.mapDerivedCategoryFactors
  refine ⟨Functor.leftDerivedUnique (LF := D.T) (LF' := D.E.mapDerivedCategory)
    D.ε D.E.mapDerivedCategoryFactors.hom W, ?_⟩
  intro M
  simp

/-- Finite-free scalar extension preserves arbitrary unbounded derived countable products
and the complete functorial Roos triangles of strict towers, including strict augmentations.
The hypothesis is only existence of a finite basis, not the choice of one. The counit equation
identifies the exact cochain model with the recorded derived tensor functor.

Source: Stacks 0A0E, 0941, 070I, 08BJ, 0BK6
(blueprint: lem-weil-pbc-finite-free-strict-tower-transport).

Proof:
1. Tensor cancellation at the unit identifies restriction of scalar extension with
   tensor by the restricted unit. A finite basis and the finite biproduct comparison
   identify this with a finite power. Exact conservative restriction therefore detects
   exactness and preservation of limits by scalar extension, also on strict towers.
2. Localize the exact ordinary scalar adjunction. Derived restriction preserves products
   and detects isomorphisms by homology. Finite powers are self-adjoint and their derived
   functors preserve products. The composite comparison proves that exact derived scalar
   extension preserves countable products, including rank zero. Left-derived uniqueness
   identifies it with the recorded derived tensor, with the specified counit equation.
3. Use the normalized resolution construction of total derived inverse limit. The absolute
   right-derived universal property constructs the comparison from the ordinary limit map;
   localization constructs the evaluation comparison. Product projections and the first
   normalization give the first Roos square on resolved towers and then on every tower.
4. An exact functor preserves the actual short-exact-sequence boundary: cancel the cone
   quasi-isomorphism and use the mapping-cone comparison, including its third arrow and
   the standard shift compatibility of the localization factorization. Ordinary limit and
   product comparisons give an isomorphism of Roos short complexes.
5. Naturality extends the target boundary formula to every tower with a short exact Roos
   sequence by passing to an injective-term K-injective resolution. Apply this to the image
   source resolution. Boundary naturality and the comparison unit equation give the last
   Roos square. Resolution naturality extends it to all derived towers. Additivity and
   product projections give the middle square.
6. The three squares form a morphism of distinguished triangles with invertible product
   components. The triangulated five lemma makes the limit comparison invertible.
   Composing its unit equation with a strict augmentation proves the augmentation equation;
   naturality gives the equation for maps of entire augmented towers.
No exactness of countable sheaf products or boundedness is used. Basis choices occur only
in proving invertibility, so the canonical comparisons are independent of them. -/
theorem finiteFreeStrictTowerTransport
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {O S : Sheaf J CommRingCat.{r}} (a : O ⟶ S)
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, w, w} a)
    (hfree : ∃ d : ℕ, Nonempty
      (free (R := derivedChangeRingIndependentCoefficients J O) (ULift.{r} (Fin d)) ≅
        (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (unit (derivedChangeRingIndependentCoefficients J S)))) :
    ∃ (_ : PreservesFiniteLimits D.E) (_ : PreservesFiniteColimits D.E)
      (_ : PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) D.E))
      (_ : PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) D.E))
      (_ : HasCountableProducts (DerivedCategory.{w} (ringedSiteModules.{r}
        (derivedChangeRingIndependentCoefficients J O))))
      (_ : HasCountableProducts (DerivedCategory.{w} (ringedSiteModules.{r}
        (derivedChangeRingIndependentCoefficients J S))))
      (κ : D.T ≅ D.E.mapDerivedCategory),
      (∀ M, D.ε.app M = κ.hom.app (DerivedCategory.Q.obj M) ≫
        D.E.mapDerivedCategoryFactors.hom.app M) ∧
      (∀ M : ℕ → DerivedCategory.{w} (ringedSiteModules.{r}
        (derivedChangeRingIndependentCoefficients J O)), IsIso (piComparison D.T M)) ∧
      Nonempty (FiniteFreeStrictTowerTransport D.E D.E.mapDerivedCategory
        (projectionPost (I := ℕᵒᵖ) D.E).mapDerivedCategory
        D.E.mapDerivedCategoryFactors
        (projectionPost (I := ℕᵒᵖ) D.E).mapDerivedCategoryFactors) := by
  classical
  let A := ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O)
  let B := ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)
  let U := restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)
  obtain ⟨hlim, hcolim⟩ := scalarFiniteExact a D hfree
  let : PreservesLimitsOfSize.{0, 0} D.E := hlim
  let : PreservesFiniteColimits D.E := hcolim
  let : PreservesFiniteLimits D.E := inferInstance
  let : PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) D.E) := by
    constructor
    intro I _ _
    exact whiskeringRight_preservesLimitsOfShape D.E
  let : PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) D.E) := by
    constructor
    intro I _ _
    exact whiskeringRight_preservesColimitsOfShape D.E
  let : IsGrothendieckAbelian.{r} A :=
    moduleSheaves_grothendieck J (derivedChangeRingIndependentCoefficients J O)
  let : IsGrothendieckAbelian.{r} B :=
    moduleSheaves_grothendieck J (derivedChangeRingIndependentCoefficients J S)
  let : IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A) := tower_grothendieck A
  let : IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ B) := tower_grothendieck B
  let : HasCountableProducts (DerivedCategory.{w} A) := derivedCountableProducts
  let : HasCountableProducts (DerivedCategory.{w} B) := derivedCountableProducts
  obtain ⟨κ, hκ⟩ := scalarExactDerivedIso a D
  obtain ⟨href, huLim, huColim⟩ := scalarRestrictionProperties
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)
  let : U.ReflectsIsomorphisms := href
  obtain ⟨huExactLim, huExactColim, ho⟩ := sheafRingCoefficientOrdinaryAdjunction a
  let : PreservesFiniteLimits U := huExactLim
  let : PreservesFiniteColimits U := huExactColim
  obtain ⟨adj, _⟩ := ho D.E D.obj_eq D.map_eq
  obtain ⟨d, ⟨e⟩⟩ := scalarFiniteCoordinates a D hfree
  have hp := finiteCoordinatesDerivedProducts D.E U adj d e
  have ht (M : ℕ → DerivedCategory.{w} A) : IsIso (piComparison D.T M) := by
    have : IsIso (piComparison D.E.mapDerivedCategory M) := hp M
    have he : piComparison D.T M = κ.hom.app (∏ᶜ M) ≫
        piComparison D.E.mapDerivedCategory M ≫
          Limits.Pi.map (fun n ↦ κ.inv.app (M n)) := by
      apply Pi.hom_ext
      intro n
      simp only [Category.assoc, Limits.Pi.map_π, piComparison_comp_π_assoc]
      rw [← κ.hom.naturality_assoc]
      simp
    rw [he]
    infer_instance
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, κ, hκ, ht, ?_⟩
  obtain ⟨LR, hLR, hnR⟩ := strictTowerNormalizedData (A := A)
  obtain ⟨LS, hLS, hnS⟩ := strictTowerNormalizedData (A := B)
  exact strictTowerTransport D.E LR LS hLR hLS hnR hnS hp

end SheafOfModules
