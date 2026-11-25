/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos
public import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedExtension
public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtension
public import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedEvaluation
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
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
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Picard.DerivedAdjunctionCompatibility

/-! # Singleton extension and arbitrary coefficient change

Source: Stacks 0D6D, lemma-derived-pullback-composition, and Zheng, Construction 4.1.
The singleton functor is an extension left adjoint, not a geometric inverse image.
(blueprint: def-pur-system-singleton-scalar-comparisons)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- The coefficient morphism on the vertical sequence site, with component a_j.
Source: Stacks 03EK; Zheng 4.1
(blueprint: def-pur-system-singleton-scalar-comparisons). -/
def singletonSequenceRingMap {B D : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : B ⟶ D) :
    systemSequenceRing B ⟶ systemSequenceRing D :=
  ⟨Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := C)).functor
    (Functor.uncurry.map (Functor.whiskerRight a (sheafToPresheaf J CommRingCat.{w})))⟩

variable (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- The existing sequence-equivalence additivity instance, with the projection exposed.
Source: Zheng 4.1 (blueprint: def-pur-system-singleton-scalar-comparisons). -/
instance singletonSequenceFunctorAdditive :
    (strictSystemSequenceEquivalence B).functor.Additive := strictSystemToSequenceAdditive B

/-- The existing inverse-equivalence additivity instance, with the projection exposed.
Source: Zheng 4.1 (blueprint: def-pur-system-singleton-scalar-comparisons). -/
instance singletonSequenceInverseAdditive :
    (strictSystemSequenceEquivalence B).inverse.Additive := sequenceToStrictSystemAdditive B

/-- Sequence-site evaluation is the inverse equivalence followed by exact evaluation,
so it preserves finite limits. Source: Zheng 4.1
(blueprint: def-pur-system-singleton-scalar-comparisons). -/
instance singletonSequenceEvaluationLimits (n : ℕ) :
    PreservesFiniteLimits (systemSequenceEvaluation B n) :=
  inferInstanceAs (PreservesFiniteLimits
    ((strictSystemSequenceEquivalence B).inverse ⋙ systemEvaluation B n))

/-- Sequence-site evaluation preserves finite colimits, for the same reason.
Source: Zheng 4.1 (blueprint: def-pur-system-singleton-scalar-comparisons). -/
instance singletonSequenceEvaluationColimits (n : ℕ) :
    PreservesFiniteColimits (systemSequenceEvaluation B n) :=
  inferInstanceAs (PreservesFiniteColimits
    ((strictSystemSequenceEquivalence B).inverse ⋙ systemEvaluation B n))

/-- The existing ordinary singleton, realized on its ringed sequence site.
Source: Zheng 4.1 (blueprint: def-pur-system-singleton-scalar-comparisons). -/
abbrev singletonSequenceOrdinary (n : ℕ) :=
  systemSingleFunctor S T B n ⋙ (strictSystemSequenceEquivalence B).functor

/-- The specified ordinary singleton adjunction transported across the sequence equivalence.
Source: Zheng 4.1 (blueprint: def-pur-system-singleton-scalar-comparisons). -/
def singletonSequenceOrdinaryAdjunction (n : ℕ) :
    singletonSequenceOrdinary S T B n ⊣ systemSequenceEvaluation B n :=
  (systemSingleAdjunction S T B n).comp (strictSystemSequenceEquivalence B).toAdjunction

/-- The existing unbounded derived singleton on the ringed sequence site.
Source: Stacks 06XN (blueprint: def-pur-system-singleton-scalar-comparisons). -/
abbrev singletonSequenceDerived (n : ℕ) :=
  (systemSingleDerivedExtension B n S T).derived ⋙
    (strictSystemSequenceEquivalence B).functor.mapDerivedCategory

/-- Its actual derived adjunction, transported along the exact-functor compositor.
Source: Stacks 0FND (blueprint: def-pur-system-singleton-scalar-comparisons). -/
def singletonSequenceDerivedAdjunction (n : ℕ) :
    singletonSequenceDerived S T B n ⊣ (systemSequenceEvaluation B n).mapDerivedCategory :=
  ((systemSingleDerivedExtension B n S T).adjunction.comp
    (strictSystemSequenceEquivalence B).mapDerivedCategory.toAdjunction).ofNatIsoRight
      (Functor.mapDerivedCategoryCompIso (strictSystemSequenceEquivalence B).inverse
        (systemEvaluation B n))

/-- The representative comparison of the transported singleton universal derived pair.
Source: Stacks 06XN (blueprint: def-pur-system-singleton-scalar-comparisons). -/
def singletonSequenceComparison (n : ℕ) (P : CochainComplex (systemLevel B n) ℤ) :
    (singletonSequenceDerived S T B n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((singletonSequenceOrdinary S T B n).mapHomologicalComplex (.up ℤ)).obj P) :=
  (strictSystemSequenceEquivalence B).functor.mapDerivedCategory.map
    ((systemSingleDerivedExtension B n S T).comparison.app P) ≫
  (strictSystemSequenceEquivalence B).functor.mapDerivedCategoryFactors.hom.app
    (((systemSingleFunctor S T B n).mapHomologicalComplex (.up ℤ)).obj P)

variable {B} {D : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : B ⟶ D)

/-- Actual scalar restriction on the sequence site.
Source: Stacks 03DA (blueprint: def-pur-system-singleton-scalar-comparisons). -/
abbrev singletonSequenceRestriction :=
  restrictScalars.{w} ((sheafCompose (coefficientSequenceTopology J)
    (forget₂ CommRingCat.{w} RingCat.{w})).map (singletonSequenceRingMap a))

/-- Actual scalar restriction at one level.
Source: Stacks 03DA (blueprint: def-pur-system-singleton-scalar-comparisons). -/
abbrev singletonLevelRestriction (n : ℕ) :=
  restrictScalars.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
    (a.app (op n)))

/-- Evaluation and restriction commute by the identity on sections.
Source: Stacks 03DA; vertical-site calculation
(blueprint: def-pur-system-singleton-scalar-comparisons). -/
def singletonRestrictionEvaluation (n : ℕ) :
    singletonSequenceRestriction a ⋙ systemSequenceEvaluation B n ≅
      systemSequenceEvaluation D n ⋙ singletonLevelRestriction a n :=
  NatIso.ofComponents (fun M ↦ (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by intros; ext x; rfl)))
    (by intros; ext U x; rfl)

variable (A : SystemScalarModel (singletonSequenceRingMap a))

/-- The ordinary comparison is the conjugate of identity-on-sections restriction.
Source: Stacks 03D7 and 03EK
(blueprint: def-pur-system-singleton-scalar-comparisons). -/
def singletonScalarOrdinaryIso (n : ℕ) :
    singletonSequenceOrdinary S T B n ⋙ A.model.E ≅
      (S (a.app (op n))).model.E ⋙ singletonSequenceOrdinary S T D n :=
  (((singletonSequenceOrdinaryAdjunction S T B n).comp A.ordinaryAdj).ofNatIsoRight
    (singletonRestrictionEvaluation a n)).leftAdjointUniq
      ((S (a.app (op n))).ordinaryAdj.comp
        (singletonSequenceOrdinaryAdjunction S T D n))

/-- Derived evaluation commutes with actual scalar restriction, using the canonical
exact-functor compositor and the identity-on-sections ordinary square.
Source: Stacks 03DA (blueprint: def-pur-system-singleton-scalar-comparisons). -/
def singletonDerivedRestrictionEvaluation (n : ℕ) :
    (singletonSequenceRestriction a).mapDerivedCategory ⋙
      (systemSequenceEvaluation B n).mapDerivedCategory ≅
    (systemSequenceEvaluation D n).mapDerivedCategory ⋙
      (singletonLevelRestriction a n).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (singletonRestrictionEvaluation a n)

/-- The displayed derived comparison, fixed by the specified composite adjunctions.
Source: Stacks 0FND and 09T5
(blueprint: def-pur-system-singleton-scalar-comparisons). -/
def singletonScalarDerivedIso (n : ℕ) :
    singletonSequenceDerived S T B n ⋙ A.model.T ≅
      (S (a.app (op n))).model.T ⋙ singletonSequenceDerived S T D n :=
  (((singletonSequenceDerivedAdjunction S T B n).comp A.adjunction).ofNatIsoRight
    (singletonDerivedRestrictionEvaluation a n)).leftAdjointUniq
      ((S (a.app (op n))).adjunction.comp
        (singletonSequenceDerivedAdjunction S T D n))

/-- The source composite's canonical map to its ordinary cochain representative.
Source: Stacks 0D6D (blueprint: def-pur-system-singleton-scalar-comparisons). -/
def singletonScalarSourceComparison (n : ℕ) (P : CochainComplex (systemLevel B n) ℤ) :=
  A.model.T.map (singletonSequenceComparison S T B n P) ≫
    A.model.ε.app (((singletonSequenceOrdinary S T B n).mapHomologicalComplex (.up ℤ)).obj P)

/-- The target composite's canonical map to its ordinary cochain representative.
Source: Stacks 0D6D (blueprint: def-pur-system-singleton-scalar-comparisons). -/
def singletonScalarTargetComparison (n : ℕ) (P : CochainComplex (systemLevel B n) ℤ) :=
  (singletonSequenceDerived S T D n).map ((S (a.app (op n))).model.ε.app P) ≫
    singletonSequenceComparison S T D n
      ((((S (a.app (op n))).model.E).mapHomologicalComplex (.up ℤ)).obj P)

/-- The canonical map from the lower singleton, transposed from evaluated L_m.
Source: Zheng 4.1; the singleton evaluation formula
(blueprint: def-pur-system-singleton-scalar-comparisons). -/
def singletonLowerMap (R : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {n m : ℕ} (h : n ≤ m)
    (P : DerivedCategory (systemLevel R m)) :
    (singletonSequenceDerived S T R n).obj ((systemDerivedTensor S R h).obj P) ⟶
      (singletonSequenceDerived S T R m).obj P :=
  (strictSystemSequenceEquivalence R).functor.mapDerivedCategory.map
    (((systemSingleDerivedExtension R n S T).adjunction.homEquiv _ _).symm
      ((systemSingleDerivedBelow R h S T).inv.app P))

/-- Scalar associativity in the square of coefficient maps, normalized by the actual
scalar restriction adjunctions, not an arbitrary isomorphism of evaluated objects.
Source: Stacks 03EK, 06YT (blueprint: def-pur-system-singleton-scalar-comparisons). -/
def singletonScalarSquare (n m : ℕ) (h : n ≤ m) :
    systemDerivedTensor S B h ⋙ (S (a.app (op n))).model.T ≅
      (S (a.app (op m))).model.T ⋙ systemDerivedTensor S D h :=
  systemScalarModelDerivedComposition rfl
    (S (B.map (homOfLE h).op)) (S (a.app (op n)))
      (S (B.map (homOfLE h).op ≫ a.app (op n))) ≪≫
  (systemScalarModelDerivedComposition (a.naturality (homOfLE h).op)
    (S (a.app (op m))) (S (D.map (homOfLE h).op))
      (S (B.map (homOfLE h).op ≫ a.app (op n)))).symm

end SheafOfModules
