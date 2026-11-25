/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalLocalizingProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalLocalizingTwist

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory

/-! # The specified Tate-twisted projection comparison
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

-- Keep fixed site and derived comparisons folded during elaboration.
/-- Tensor with the given degree-zero Tate module, followed by the positive shift two. -/
def twist (X : Scheme.{u}) (L : Modules Λ X) :
    DerivedCategory (Modules Λ X) ⥤ DerivedCategory (Modules Λ X) :=
  rationalTwistFunctor Λ X L ⋙ shiftFunctor _ (2 : ℤ)

/-- The native tensor-shift comparison in the shared interface is uniquely determined. -/
theorem tensorShift_existsUnique (X : Scheme.{u}) (L : Modules Λ X)
    (A : DerivedCategory (Modules Λ X)) :
    ∃! e : A ⊗ (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj L) ⟦(2 : ℤ)⟧) ≅
        (twist Λ X L).obj A,
      HEq e (((tensorLeft A).commShiftIso (2 : ℤ)).app
        ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj L)) := by
  unfold internalMonoidal internalTensorBundle nativeTensorBundle
  dsimp only [twist, rationalTwistFunctor, CondensedRing.derivedTensor, Functor.comp_obj]
  refine ⟨_, HEq.rfl, ?_⟩
  intro e he
  exact eq_of_heq he

/-- The fixed native tensor-shift comparison, with the Tate factor on the right. -/
def tensorShiftIso (X : Scheme.{u}) (L : Modules Λ X)
    (A : DerivedCategory (Modules Λ X)) :
    A ⊗ (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj L) ⟦(2 : ℤ)⟧) ≅
      (twist Λ X L).obj A :=
  (tensorShift_existsUnique Λ X L A).exists.choose

/-- The family of canonical right-factor projection arrows in the shared tensor interface. -/
def ProjectionMateFamily := ∀ {X S : Scheme.{u}} (f : X ⟶ S)
  (A : DerivedCategory (Modules Λ X)) (B : DerivedCategory (Modules Λ S)),
  (moduleObjectDerivedPushforward Λ f).obj A ⊗ B ⟶
    (moduleObjectDerivedPushforward Λ f).obj (A ⊗ (moduleObjectDerivedPullback Λ f).obj B)

/-- Retain the representative-normalized projection mate, pointwise. -/
def ProjectionMateNormalized (a : ProjectionMateFamily Λ) : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (A : DerivedCategory (Modules Λ X))
    (B : DerivedCategory (Modules Λ S)), HEq (a f A B) (moduleObjectProjectionMate Λ f A B)

/-- The mate uniquely determines the family in the shared interface. -/
theorem projectionMate_existsUnique :
    ∃! a : ProjectionMateFamily Λ, ProjectionMateNormalized Λ a := by
  unfold ProjectionMateFamily ProjectionMateNormalized
  unfold internalMonoidal internalTensorBundle nativeTensorBundle
  refine ⟨fun {_ _} f A B ↦ moduleObjectProjectionMate Λ f A B, ?_, ?_⟩
  · intro X S f A B
    exact HEq.rfl
  · intro a ha
    funext X S f A B
    exact eq_of_heq (ha f A B)

/-- The same projection mate in the fixed shared interface. -/
def projectionMateMap : ProjectionMateFamily Λ := (projectionMate_existsUnique Λ).exists.choose

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The right projection mate with precisely the specified shifted-line comparison. -/
def twistProjectionMap {X S : Scheme.{u}} (f : X ⟶ S)
    (LS : Modules Λ S) (LX : Modules Λ X)
    (e : (moduleObjectDerivedPullback Λ f).obj
      (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧)
    (A : DerivedCategory (Modules Λ X)) :
    (twist Λ S LS).obj ((moduleObjectDerivedPushforward Λ f).obj A) ⟶
      (moduleObjectDerivedPushforward Λ f).obj ((twist Λ X LX).obj A) :=
  (tensorShiftIso Λ S LS _).inv ≫
    projectionMateMap Λ f A
      (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧) ≫
    (moduleObjectDerivedPushforward Λ f).map
      ((A ◁ e.hom) ≫ (tensorShiftIso Λ X LX A).hom)

end AlgebraicGeometry.ProEtale.RationalP1
