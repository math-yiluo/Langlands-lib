/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtension

/-!
# Scalar extension with its normalized derived adjunction

Source: Stacks Project, Tags 06YY, 06XN and 09T5.
(blueprint: lem-pur-coefficient-scalar-derived-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w d
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules
private theorem scalarDerivedModel
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B]
    (E : A ⥤ B) (R : B ⥤ A) [E.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (adj : E ⊣ R) (P : CochainComplex A ℤ → Prop)
    (hres : ∀ X, ∃ (Y : CochainComplex A ℤ) (s : Y ⟶ X), P Y ∧ QuasiIso s)
    (hpres : ∀ {X Y} (f : X ⟶ Y), P X → P Y → QuasiIso f →
      QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f)) :
    Nonempty (DerivedCoefficientScalarExtension E R adj P) := by
  obtain ⟨_, L, ε, hu, hc, a, ha⟩ :=
    CategoryTheory.Adjunction.exists_leftDerived_adjunction E R adj P hres hpres
  exact ⟨{
    derived := L
    counit := ε
    isDerived := hu
    computes := hc
    restriction := R.mapDerivedCategory
    restrictionFactors := R.mapDerivedCategoryFactors
    derivedAdj := a
    transpose := ha }⟩

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C]
  {O : Type w} [CommRing O] {ell : O}
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

omit [EssentiallySmall.{w} C] [∀ n : ℕ, HasDerivedCategory.{d}
  (coefficientLevelModules (J := J) O ell n)] in
private theorem coefficient_quasiIso_transport
    {m n : ℕ}
    (E F : coefficientLevelModules (J := J) O ell m ⥤
      coefficientLevelModules (J := J) O ell n) [E.Additive] [F.Additive] (h : E = F)
    {P Q : CochainComplex (coefficientLevelModules (J := J) O ell m) ℤ} (f : P ⟶ Q)
    (hf : QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  cases h
  exact hf

omit [EssentiallySmall.{w} C] [∀ n : ℕ, HasDerivedCategory.{d}
  (coefficientLevelModules (J := J) O ell n)] in
private theorem coefficientRestriction_exact {m n : ℕ} (h : n ≤ m) :
    PreservesFiniteLimits (coefficientRestriction (J := J) O ell h) ∧
      PreservesFiniteColimits (coefficientRestriction (J := J) O ell h) := by
  exact systemScalarRestriction_exact (coefficientQuotientMap (J := J) O ell h)

private theorem coefficientTensor_quasiIso {m n : ℕ} (h : n ≤ m)
    {P Q : CochainComplex (coefficientLevelModules (J := J) O ell m) ℤ} (f : P ⟶ Q)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (hf : QuasiIso f) : QuasiIso
      (((coefficientTensor (J := J) (O := O) (ell := ell) h).mapHomologicalComplex
        (.up ℤ)).map f) := by
  obtain ⟨E, hobj, hmap, _, hpres, _⟩ :=
    derivedChangeOfRingsIndependentCoefficients (coefficientQuotientMap (J := J) O ell h)
  have hE : E = coefficientTensor (J := J) (O := O) (ell := ell) h := by
    refine CategoryTheory.Functor.ext hobj ?_
    intro M N f
    exact hmap f
  exact coefficient_quasiIso_transport E _ hE f (hpres f hP hQ hf)

/-- The fixed quotient tensor functor has a universal derived scalar extension,
computed on every K-flat complex, whose adjunction respects the specified ordinary
adjunction on all complex representatives.
Source: Stacks Project, Tags 06YY, 06XN and 09T5
(blueprint: lem-pur-coefficient-scalar-derived-adjunction).
Proof: identify the pointwise tensor functor with the change-of-rings functor in the
independent-coefficient theorem by its object and morphism formulas. That theorem
shows preservation of quasi-isomorphisms between K-flat complexes. Every complex has
a K-flat resolution. Restriction of scalars is exact. Apply the resolving-class derived
adjunction theorem with the fixed ordinary tensor adjunction, retaining its normalized
transpose formula and its comparison isomorphism on every K-flat representative. -/
theorem coefficientScalarDerivedAdjunction {m n : ℕ} (h : n ≤ m) :
    Nonempty (DerivedCoefficientScalarExtension
      (coefficientTensor (J := J) (O := O) (ell := ell) h)
      (coefficientRestriction (J := J) O ell h)
      (coefficientTensorAdj (J := J) (O := O) (ell := ell) h)
      (CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientQuotientSheaf (J := J) O ell m))) := by
  let := (coefficientRestriction_exact (J := J) (O := O) (ell := ell) h).1
  let := (coefficientRestriction_exact (J := J) (O := O) (ell := ell) h).2
  exact scalarDerivedModel
      (coefficientTensor (J := J) (O := O) (ell := ell) h)
      (coefficientRestriction (J := J) O ell h)
      (coefficientTensorAdj (J := J) (O := O) (ell := ell) h)
      (CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientQuotientSheaf (J := J) O ell m))
      (fun X ↦ by
        obtain ⟨Y, s, hY, _, hs, _⟩ :=
          CochainComplex.exists_isKFlatResolutionIndependentCoefficients X
        exact ⟨Y, s, hY, hs⟩)
      (fun f hP hQ hf ↦ coefficientTensor_quasiIso h f hP hQ hf)

/-- The family of universal derived quotient scalar extensions.
Source: Stacks Tags 06YY and 09T5
(blueprint: lem-pur-coefficient-scalar-derived-adjunction). -/
abbrev CoefficientScalarDerivedAssignment :=
  ∀ {m n : ℕ} (h : n ≤ m), DerivedCoefficientScalarExtension
    (coefficientTensor (J := J) (O := O) (ell := ell) h)
    (coefficientRestriction (J := J) O ell h)
    (coefficientTensorAdj (J := J) (O := O) (ell := ell) h)
    ((CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientQuotientSheaf (J := J) O ell m)))

end SheafOfModules
