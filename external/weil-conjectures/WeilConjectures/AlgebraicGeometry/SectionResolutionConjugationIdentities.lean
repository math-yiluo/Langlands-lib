/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
import all WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
public import WeilConjectures.AlgebraicGeometry.SectionKFlatTensorComparison
public import WeilConjectures.AlgebraicGeometry.SectionOplaxTotalComparison
public import WeilConjectures.AlgebraicGeometry.SectionRepresentativeTensorArrow
public import WeilConjectures.Topology.ProfiniteCondensedRing

/-! # Resolution conjugation identities for the section equivalence

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E; the explicit
internal/section conjugation calculation in the blueprint proof
(auxiliary; not a blueprint node).

The maps below are composites of the specified comparisons, never independently
chosen tensor-pullback transformations. Composition in Lean is left to right.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
attribute [local irreducible] tensorComparison qTensor tensor Functor.mapDerivedCategory
  derivedFunctor derivedPullback internalDerivedPullFunctor
  derivedSectionFunctor internalLocalizationFunctor
set_option allowUnsafeReducibility true in
attribute [local irreducible] DerivedMonoidal.tensorObjAux
  DerivedMonoidal.whiskerLeftAux DerivedMonoidal.whiskerRightAux
attribute [local irreducible] CategoryTheory.Localization.Monoidal.tensorBifunctor
  CategoryTheory.DerivedMonoidal.bifunctor

namespace ResolutionConjugation
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

/-- The internal resolution transformation eta at a cochain representative.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def eta {X Y : Scheme.{u}} (f : X ⟶ Y) (A : CochainComplex (internalModules Λ Y) ℤ) :
    (internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj A) ⟶
      (internalLocalizationFunctor Λ X).obj ((totalInternalPull Λ f).obj A) :=
  by
    with_unfolding_all
      exact cast (by rfl) ((CondensedRing.upperStar Λ f).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj A))

/-- The specified section resolution transformation epsilon, using exact localization.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def epsilon {X Y : Scheme.{u}} (f : X ⟶ Y) (P : CochainComplex (modules Λ Y) ℤ) :
    (derivedPullback Λ f).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((totalSectionPull Λ f).obj P) :=
  by
    with_unfolding_all exact (pullback Λ f).mapDerivedCategoryFactors.hom.app P

/-- The output identification d_A = q(h_A) kappa at the internal pullback.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def d {X Y : Scheme.{u}} (f : X ⟶ Y) (A : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedSectionFunctor Λ X).obj
        ((internalLocalizationFunctor Λ X).obj ((totalInternalPull Λ f).obj A)) ⟶
      DerivedCategory.Q.obj ((totalSectionPull Λ f).obj
        ((totalSectionEquivalence Λ Y).obj A)) :=
  (cochainLocalizationIso Λ X ((totalInternalPull Λ f).obj A)).hom ≫
    DerivedCategory.Q.map (termwisePullComparison Λ f A).hom

/-- The input identification j_A = LF(kappa_A) gamma.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def j {X Y : Scheme.{u}} (f : X ⟶ Y) (A : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedSectionFunctor Λ X).obj
        ((internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj A)) ⟶
      (derivedPullback Λ f).obj
        (DerivedCategory.Q.obj ((totalSectionEquivalence Λ Y).obj A)) :=
  (derivedPullSquare Λ f).hom.app ((internalLocalizationFunctor Λ Y).obj A) ≫
    (derivedPullback Λ f).map (cochainLocalizationIso Λ Y A).hom

/-- The total input-output identification d_Z, including F applied to the total comparison.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def dZ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedSectionFunctor Λ X).obj
        ((internalLocalizationFunctor Λ X).obj ((totalInternalPull Λ f).obj (A ⊗ B))) ⟶
      DerivedCategory.Q.obj ((totalSectionPull Λ f).obj
        ((totalSectionEquivalence Λ Y).obj A ⊗ (totalSectionEquivalence Λ Y).obj B)) :=
  d Λ f (A ⊗ B) ≫
    DerivedCategory.Q.map ((totalSectionPull Λ f).map (cochainTensorComparison Λ Y A B).hom)

/-- The total output identification d_out, with the tensor of the ordinary pull comparisons.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def dOut {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedSectionFunctor Λ X).obj ((internalLocalizationFunctor Λ X).obj
        ((totalInternalPull Λ f).obj A ⊗ (totalInternalPull Λ f).obj B)) ⟶
      DerivedCategory.Q.obj
        ((totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj A) ⊗
          (totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj B)) :=
  (cochainLocalizationIso Λ X
      ((totalInternalPull Λ f).obj A ⊗ (totalInternalPull Λ f).obj B)).hom ≫
    DerivedCategory.Q.map (cochainTensorComparison Λ X
      ((totalInternalPull Λ f).obj A) ((totalInternalPull Λ f).obj B)).hom ≫
    DerivedCategory.Q.map
      ((termwisePullComparison Λ f A).hom ⊗ₘ (termwisePullComparison Λ f B).hom)

/-- The binary input identification j_AB, with the fixed theta followed by kappa tensor kappa.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def jTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedSectionFunctor Λ X).obj ((internalDerivedPullFunctor Λ f).obj
        ((internalLocalizationFunctor Λ Y).obj A ⊗ (internalLocalizationFunctor Λ Y).obj B)) ⟶
      (derivedPullback Λ f).obj ((tensor Λ Y).obj
        (DerivedCategory.Q.obj ((totalSectionEquivalence Λ Y).obj A),
          DerivedCategory.Q.obj ((totalSectionEquivalence Λ Y).obj B))) :=
  (derivedPullSquare Λ f).hom.app ((internalLocalizationFunctor Λ Y).obj A ⊗
      (internalLocalizationFunctor Λ Y).obj B) ≫
    (derivedPullback Λ f).map
      ((derivedSectionTensorIso Λ Y ((internalLocalizationFunctor Λ Y).obj A)
          ((internalLocalizationFunctor Λ Y).obj B)).hom ≫
        (tensor Λ Y).map (Prod.mkHom (cochainLocalizationIso Λ Y A).hom
          (cochainLocalizationIso Λ Y B).hom))

/-- The binary output identification k_AB, in the order theta, gamma tensor gamma, LF(kappa).
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def kTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedSectionFunctor Λ X).obj
        ((internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj A) ⊗
          (internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj B)) ⟶
      (tensor Λ X).obj
        ((derivedPullback Λ f).obj
            (DerivedCategory.Q.obj ((totalSectionEquivalence Λ Y).obj A)),
          (derivedPullback Λ f).obj
            (DerivedCategory.Q.obj ((totalSectionEquivalence Λ Y).obj B))) :=
  (derivedSectionTensorIso Λ X
    ((internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj A))
    ((internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj B))).hom ≫
    (tensor Λ X).map (Prod.mkHom
      ((derivedPullSquare Λ f).hom.app ((internalLocalizationFunctor Λ Y).obj A))
      ((derivedPullSquare Λ f).hom.app ((internalLocalizationFunctor Λ Y).obj B))) ≫
    (tensor Λ X).map (Prod.mkHom
      ((derivedPullback Λ f).map (cochainLocalizationIso Λ Y A).hom)
      ((derivedPullback Λ f).map (cochainLocalizationIso Λ Y B).hom))

/-- The internal input arrow a^i. The lax localization map is (r_Y^i) inverse.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def aInternal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj A ⊗
        (internalLocalizationFunctor Λ Y).obj B) ⟶
      (internalLocalizationFunctor Λ X).obj ((totalInternalPull Λ f).obj (A ⊗ B)) :=
  (internalDerivedPullFunctor Λ f).map
      (internalQTensorArrow Λ Y A B) ≫
    eta Λ f (A ⊗ B)

/-- The internal output arrow c^i; its final lax localization map is (r_X^i) inverse.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def cInternal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj A) ⊗
        (internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj B) ⟶
      (internalLocalizationFunctor Λ X).obj
        ((totalInternalPull Λ f).obj A ⊗ (totalInternalPull Λ f).obj B) :=
  (eta Λ f A ⊗ₘ eta Λ f B) ≫
    internalQTensorArrow Λ X
      ((totalInternalPull Λ f).obj A) ((totalInternalPull Λ f).obj B)

/-- The section input arrow a^s, with the prescribed inverse representative map qTensor.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def aSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    (derivedPullback Λ f).obj
        ((tensor Λ Y).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ⟶
      DerivedCategory.Q.obj ((totalSectionPull Λ f).obj (P ⊗ Q)) :=
  (derivedPullback Λ f).map (qTensorArrow Λ Y P Q) ≫
    epsilon Λ f (P ⊗ Q)

/-- The section output arrow c^s, using the fixed tensor on epsilon and then qTensor.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def cSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    (tensor Λ X).obj
        ((derivedPullback Λ f).obj (DerivedCategory.Q.obj P),
          (derivedPullback Λ f).obj (DerivedCategory.Q.obj Q)) ⟶
      DerivedCategory.Q.obj ((totalSectionPull Λ f).obj P ⊗ (totalSectionPull Λ f).obj Q) :=
  (tensor Λ X).map (Prod.mkHom (epsilon Λ f P) (epsilon Λ f Q)) ≫
    qTensorArrow Λ X ((totalSectionPull Λ f).obj P) ((totalSectionPull Λ f).obj Q)

/-- The regular unit identification e_T = q(ell_T) kappa_{R_T[0]}.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def e (T : Scheme.{u}) :
    (derivedSectionFunctor Λ T).obj
        ((internalLocalizationFunctor Λ T).obj (internalCochainUnit Λ T)) ⟶
      DerivedCategory.Q.obj (sectionCochainUnit Λ T) :=
  (cochainLocalizationIso Λ T (internalCochainUnit Λ T)).hom ≫
    DerivedCategory.Q.map (cochainUnitComparison Λ T).hom

/-- The three resolution equations and the localized actual total-arrow equation.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def Equations {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) : Prop :=
  ((derivedSectionFunctor Λ X).map (eta Λ f A) ≫ d Λ f A =
    j Λ f A ≫ epsilon Λ f ((totalSectionEquivalence Λ Y).obj A)) ∧
  ((derivedSectionFunctor Λ X).map (aInternal Λ f A B) ≫ dZ Λ f A B =
    jTensor Λ f A B ≫ aSection Λ f ((totalSectionEquivalence Λ Y).obj A)
      ((totalSectionEquivalence Λ Y).obj B)) ∧
  ((derivedSectionFunctor Λ X).map (cInternal Λ f A B) ≫ dOut Λ f A B =
    kTensor Λ f A B ≫ cSection Λ f ((totalSectionEquivalence Λ Y).obj A)
      ((totalSectionEquivalence Λ Y).obj B)) ∧
  ((derivedSectionFunctor Λ X).map
      ((internalLocalizationFunctor Λ X).map (actualInternalTotalIso Λ f A B).hom) ≫ dOut Λ f A B =
    dZ Λ f A B ≫ DerivedCategory.Q.map
      (sectionTotalIso Λ f ((totalSectionEquivalence Λ Y).obj A)
        ((totalSectionEquivalence Λ Y).obj B)).hom)

/-- The unary formula with the localized ordinary regular-unit comparison.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def UnitEquation {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  (derivedSectionFunctor Λ X).map
      (eta Λ f (internalCochainUnit Λ Y) ≫
        (internalLocalizationFunctor Λ X).map (internalPullUnitArrow Λ f)) ≫ e Λ X =
    (derivedPullSquare Λ f).hom.app
        ((internalLocalizationFunctor Λ Y).obj (internalCochainUnit Λ Y)) ≫
      (derivedPullback Λ f).map (e Λ Y) ≫
      epsilon Λ f (sectionCochainUnit Λ Y) ≫
      DerivedCategory.Q.map (sectionPullUnitArrow Λ f)

/-- Naturality of the four displayed composites on resolving representatives. The matching
right-hand composites are equal by Equations, so these are also their naturality squares.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def Naturality {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (A B A' B' : CochainComplex (internalModules Λ Y) ℤ)
      (_hA : KFlatSectionComparison.internalResolving Λ Y A)
      (_hB : KFlatSectionComparison.internalResolving Λ Y B)
      (_hA' : KFlatSectionComparison.internalResolving Λ Y A')
      (_hB' : KFlatSectionComparison.internalResolving Λ Y B') (a : A ⟶ A') (b : B ⟶ B'),
    ((derivedSectionFunctor Λ X).map
          ((internalDerivedPullFunctor Λ f).map ((internalLocalizationFunctor Λ Y).map a)) ≫
        (derivedSectionFunctor Λ X).map (eta Λ f A') ≫ d Λ f A' =
      (derivedSectionFunctor Λ X).map (eta Λ f A) ≫ d Λ f A ≫
        DerivedCategory.Q.map
          ((totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map a))) ∧
    ((derivedSectionFunctor Λ X).map ((internalDerivedPullFunctor Λ f).map
          ((internalLocalizationFunctor Λ Y).map a ⊗ₘ (internalLocalizationFunctor Λ Y).map b)) ≫
        (derivedSectionFunctor Λ X).map (aInternal Λ f A' B') ≫ dZ Λ f A' B' =
      (derivedSectionFunctor Λ X).map (aInternal Λ f A B) ≫ dZ Λ f A B ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map
          ((totalSectionEquivalence Λ Y).map a ⊗ₘ (totalSectionEquivalence Λ Y).map b))) ∧
    ((derivedSectionFunctor Λ X).map
          ((internalDerivedPullFunctor Λ f).map ((internalLocalizationFunctor Λ Y).map a) ⊗ₘ
            (internalDerivedPullFunctor Λ f).map ((internalLocalizationFunctor Λ Y).map b)) ≫
        (derivedSectionFunctor Λ X).map (cInternal Λ f A' B') ≫ dOut Λ f A' B' =
      (derivedSectionFunctor Λ X).map (cInternal Λ f A B) ≫ dOut Λ f A B ≫
        DerivedCategory.Q.map
          ((totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map a) ⊗ₘ
            (totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map b))) ∧
    ((derivedSectionFunctor Λ X).map
          ((internalLocalizationFunctor Λ X).map ((totalInternalPull Λ f).map (a ⊗ₘ b))) ≫
        (derivedSectionFunctor Λ X).map
          ((internalLocalizationFunctor Λ X).map (actualInternalTotalIso Λ f A' B').hom) ≫ dOut
              Λ f A' B' =
      (derivedSectionFunctor Λ X).map
          ((internalLocalizationFunctor Λ X).map (actualInternalTotalIso Λ f A B).hom) ≫ dOut Λ
              f A B ≫
        DerivedCategory.Q.map
          ((totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map a) ⊗ₘ
            (totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map b)))

/-- Substitution by the displayed section equivalence isomorphisms. Every transport
is written explicitly, so the equations at arbitrary section representatives retain
exactly the original comparison factors.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def SubstitutionEquations {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ)
    (P Q : CochainComplex (modules Λ Y) ℤ)
    (σ : (totalSectionEquivalence Λ Y).obj A ≅ P)
    (τ : (totalSectionEquivalence Λ Y).obj B ≅ Q) : Prop :=
  ((derivedSectionFunctor Λ X).map (eta Λ f A) ≫ d Λ f A ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map σ.hom) =
      j Λ f A ≫ (derivedPullback Λ f).map (DerivedCategory.Q.map σ.hom) ≫
        epsilon Λ f P) ∧
  ((derivedSectionFunctor Λ X).map (aInternal Λ f A B) ≫ dZ Λ f A B ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map (σ.hom ⊗ₘ τ.hom)) =
      jTensor Λ f A B ≫ (derivedPullback Λ f).map
          ((tensor Λ Y).map (Prod.mkHom (DerivedCategory.Q.map σ.hom)
            (DerivedCategory.Q.map τ.hom))) ≫ aSection Λ f P Q) ∧
  ((derivedSectionFunctor Λ X).map (cInternal Λ f A B) ≫ dOut Λ f A B ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map σ.hom ⊗ₘ
          (totalSectionPull Λ f).map τ.hom) =
      kTensor Λ f A B ≫ (tensor Λ X).map (Prod.mkHom
          ((derivedPullback Λ f).map (DerivedCategory.Q.map σ.hom))
          ((derivedPullback Λ f).map (DerivedCategory.Q.map τ.hom))) ≫ cSection Λ f P Q) ∧
  ((derivedSectionFunctor Λ X).map
        ((internalLocalizationFunctor Λ X).map (actualInternalTotalIso Λ f A B).hom) ≫ dOut Λ f
            A B ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map σ.hom ⊗ₘ
          (totalSectionPull Λ f).map τ.hom) =
      dZ Λ f A B ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map (σ.hom ⊗ₘ τ.hom)) ≫
        DerivedCategory.Q.map (sectionTotalIso Λ f P Q).hom)

/-- The unary equation after substituting a section-unit isomorphism. In the theorem
this is exactly the inverse of the termwise equivalence counit at the section unit.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def UnitSubstitution {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (modules Λ Y) ℤ)
    (σ : sectionCochainUnit Λ Y ≅ P) : Prop :=
  (derivedSectionFunctor Λ X).map
      (eta Λ f (internalCochainUnit Λ Y) ≫
        (internalLocalizationFunctor Λ X).map (internalPullUnitArrow Λ f)) ≫ e Λ X =
    (derivedPullSquare Λ f).hom.app
        ((internalLocalizationFunctor Λ Y).obj (internalCochainUnit Λ Y)) ≫
      (derivedPullback Λ f).map (e Λ Y ≫ DerivedCategory.Q.map σ.hom) ≫
      epsilon Λ f P ≫ DerivedCategory.Q.map
        ((totalSectionPull Λ f).map σ.inv ≫ sectionPullUnitArrow Λ f)

set_option allowUnsafeReducibility true in
attribute [local reducible] comparisonSource

private theorem map_pair_comp_assoc
    {C D : Type*} [Category* C] [Category* D] (F : C × C ⥤ D)
    {A B C' A' B' C'' : C} (a : A ⟶ B) (b : A' ⟶ B')
    (c : B ⟶ C') (d : B' ⟶ C'') {V : D} (k : F.obj (C', C'') ⟶ V) :
    F.map (Prod.mkHom a b) ≫ F.map (Prod.mkHom c d) ≫ k =
      F.map (Prod.mkHom (a ≫ c) (b ≫ d)) ≫ k := by
  rw [← F.map_comp_assoc]
  rfl

private theorem reverse_assoc_square {C : Type*} [Category* C]
    {A B D E : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    {v : A ⟶ E} (h : a ≫ b ≫ c = v) : v = (a ≫ b) ≫ c :=
  h.symm.trans (Category.assoc a b c).symm

private theorem input_calculation
    {B C D E : Type*} [Category* B] [Category* C] [Category* D] [Category* E]
    (G : C ⥤ D) (L : B ⥤ C) (H : B ⥤ E) (F : E ⥤ D)
    (γ : L ⋙ G ⟶ H ⋙ F)
    {U V : B} {W : C} {P Q K : E} {S R : D}
    (μ : U ⟶ V) (η : L.obj V ⟶ W) (d : G.obj W ⟶ S) (z : S ⟶ R)
    (κ : H.obj V ⟶ P) (k : H.obj U ⟶ K) (s : P ⟶ Q) (q : K ⟶ Q)
    (εP : F.obj P ⟶ S) (εQ : F.obj Q ⟶ R)
    (hη : G.map η ≫ d = γ.app V ≫ F.map κ ≫ εP)
    (hε : F.map s ≫ εQ = εP ≫ z)
    (hr : H.map μ ≫ κ ≫ s = k ≫ q) :
    G.map (L.map μ ≫ η) ≫ d ≫ z =
      (γ.app U ≫ F.map k) ≫ (F.map q ≫ εQ) := by
  have hn := γ.naturality μ
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hη, hε.symm, reassoc_of% hn]
  rw [← F.map_comp_assoc, ← F.map_comp_assoc, Category.assoc, hr]
  simp only [Functor.map_comp, Category.assoc]

private theorem output_calculation
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategoryStruct C]
    (G : C ⥤ D) (T : D × D ⥤ D)
    (θ : ∀ U V : C, G.obj (U ⊗ V) ⟶ T.obj (G.obj U, G.obj V))
    (hθ : ∀ {U U' V V' : C} (a : U ⟶ U') (b : V ⟶ V'),
      G.map (a ⊗ₘ b) ≫ θ U' V' = θ U V ≫ T.map (Prod.mkHom (G.map a) (G.map b)))
    {U U' V V' W : C} {Z R₀ R P Q P' Q' LA LB MA MB : D}
    (η : U ⟶ U') (ζ : V ⟶ V') (μ : U' ⊗ V' ⟶ W)
    (κZ : G.obj W ⟶ Z) (t : Z ⟶ R₀) (z : R₀ ⟶ R)
    (κA : G.obj U' ⟶ P) (κB : G.obj V' ⟶ Q)
    (a : P ⟶ P') (b : Q ⟶ Q') (q₀ : T.obj (P, Q) ⟶ R₀)
    (q : T.obj (P', Q') ⟶ R)
    (γA : G.obj U ⟶ LA) (γB : G.obj V ⟶ LB)
    (lA : LA ⟶ MA) (lB : LB ⟶ MB) (εA : MA ⟶ P') (εB : MB ⟶ Q')
    (hr : G.map μ ≫ κZ ≫ t = θ U' V' ≫ T.map (Prod.mkHom κA κB) ≫ q₀)
    (hq : T.map (Prod.mkHom a b) ≫ q = q₀ ≫ z)
    (hA : G.map η ≫ κA ≫ a = γA ≫ lA ≫ εA)
    (hB : G.map ζ ≫ κB ≫ b = γB ≫ lB ≫ εB) :
    G.map ((η ⊗ₘ ζ) ≫ μ) ≫ κZ ≫ t ≫ z =
      (θ U V ≫ T.map (Prod.mkHom γA γB) ≫ T.map (Prod.mkHom lA lB)) ≫
        (T.map (Prod.mkHom εA εB) ≫ q) := by
  have hn := hθ η ζ
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hr, hq.symm, reassoc_of% hn]
  simp only [map_pair_comp_assoc]
  rw [hA, hB]

private theorem map_square {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B C' D' : C} {a : A ⟶ B} {b : B ⟶ D'} {c : A ⟶ C'} {d : C' ⟶ D'}
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d := by
  simpa only [Functor.map_comp] using congrArg F.map h

private theorem paste_mapped_triple
    {C D : Type*} [Category* C] [Category* D] (R : C ⥤ D)
    {A B C' D' E F : C} {U V : D}
    {a : U ⟶ V} {k : V ⟶ R.obj B} {l : U ⟶ R.obj A}
    {c₀ : A ⟶ B} {c₁ : B ⟶ C'} {c₂ : C' ⟶ D'}
    {d₀ : A ⟶ E} {d₁ : E ⟶ F} {d₂ : F ⟶ D'}
    (hn : a ≫ k = l ≫ R.map c₀) (h : c₀ ≫ c₁ ≫ c₂ = d₀ ≫ d₁ ≫ d₂) :
    a ≫ (k ≫ R.map c₁ ≫ R.map c₂) = ((l ≫ R.map d₀) ≫ R.map d₁) ≫ R.map d₂ := by
  have hm : R.map c₀ ≫ R.map c₁ ≫ R.map c₂ =
      R.map d₀ ≫ R.map d₁ ≫ R.map d₂ := by
    simpa only [Functor.map_comp] using congrArg R.map h
  simp only [Category.assoc]
  rw [← Category.assoc a k (R.map c₁ ≫ R.map c₂), hn, Category.assoc, hm]

private theorem paste {C : Type*} [Category* C] {A B D E F G : C}
    {a : A ⟶ B} {b : A ⟶ D} {c : B ⟶ E} {d : D ⟶ E}
    {e : D ⟶ F} {f : E ⟶ G} {g : F ⟶ G}
    (h : a ≫ c = b ≫ d) (k : d ≫ f = e ≫ g) :
    a ≫ (c ≫ f) = (b ≫ e) ≫ g := by
  rw [← Category.assoc, h, Category.assoc, k, Category.assoc]

private theorem paste_right {C : Type*} [Category* C] {A B D E F G : C}
    {a : A ⟶ B} {b : A ⟶ D} {c : B ⟶ E} {d : D ⟶ E}
    {e : D ⟶ F} {f : E ⟶ G} {g : F ⟶ G}
    (h : a ≫ c = b ≫ d) (k : d ≫ f = e ≫ g) :
    a ≫ c ≫ f = b ≫ e ≫ g := by
  simpa only [Category.assoc] using paste h k

private theorem tensor_square {C : Type*} [Category* C] [MonoidalCategory C]
    {A B D E A' B' D' E' : C}
    {a : A ⟶ B} {b : B ⟶ E} {c : A ⟶ D} {d : D ⟶ E}
    {a' : A' ⟶ B'} {b' : B' ⟶ E'} {c' : A' ⟶ D'} {d' : D' ⟶ E'}
    (h : a ≫ b = c ≫ d) (k : a' ≫ b' = c' ≫ d') :
    (a ⊗ₘ a') ≫ (b ⊗ₘ b') = (c ⊗ₘ c') ≫ (d ⊗ₘ d') := by
  simp only [tensorHom_comp_tensorHom, h, k]

private theorem pair_square {C : Type*} [Category* C]
    {A B D E A' B' D' E' : C}
    {a : A ⟶ B} {b : B ⟶ E} {c : A ⟶ D} {d : D ⟶ E}
    {a' : A' ⟶ B'} {b' : B' ⟶ E'} {c' : A' ⟶ D'} {d' : D' ⟶ E'}
    (h : a ≫ b = c ≫ d) (k : a' ≫ b' = c' ≫ d') :
    Prod.mkHom a a' ≫ Prod.mkHom b b' = Prod.mkHom c c' ≫ Prod.mkHom d d' := by
  ext
  · exact h
  · exact k

private theorem substitute_square {C : Type*} [Category* C]
    {A B D E F G : C} {a : A ⟶ B} {b : B ⟶ E} {c : A ⟶ D} {d : D ⟶ E}
    {t : E ⟶ G} {s : D ⟶ F} {e : F ⟶ G}
    (h : a ≫ b = c ≫ d) (k : s ≫ e = d ≫ t) :
    a ≫ b ≫ t = c ≫ s ≫ e := by
  rw [← Category.assoc, h, Category.assoc, ← k]

private theorem unit_iso_transport
    {B C D E : Type*} [Category* B] [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (Q : B ⥤ C) (S : B ⥤ E) (R : E ⥤ D)
    {P P' : B} {U : C} {A : D} {W : E}
    (γ : A ⟶ F.obj U) (k : U ⟶ Q.obj P) (σ : P ≅ P')
    (ε : F.obj (Q.obj P) ⟶ R.obj (S.obj P))
    (ε' : F.obj (Q.obj P') ⟶ R.obj (S.obj P')) (t : S.obj P ⟶ W)
    (h : F.map (Q.map σ.hom) ≫ ε' = ε ≫ R.map (S.map σ.hom)) :
    γ ≫ F.map k ≫ ε ≫ R.map t =
      γ ≫ F.map (k ≫ Q.map σ.hom) ≫ ε' ≫ R.map (S.map σ.inv ≫ t) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h]
  rw [← R.map_comp_assoc, ← S.map_comp, Iso.hom_inv_id]
  simp only [S.map_id, R.map_id, Category.id_comp]

private theorem undo_explicit_conjugation
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (F : A ⥤ B) (G : C ⥤ B) {x y : A} {u v : C} {w t : B}
    (p : x ≅ y) (r : G.obj u ≅ F.obj x) (i : u ≅ v)
    (c : G.obj v ≅ w) (e : w ≅ t) (h : F.obj y ⟶ t)
    (hh : F.map p.inv ≫ r.inv ≫ G.map i.hom ≫ c.hom ≫ e.hom = h) :
    G.map i.hom ≫ c.hom ≫ e.hom = r.hom ≫ F.map p.hom ≫ h := by
  rw [← hh]
  simp only [← F.map_comp_assoc, Iso.hom_inv_id,
    F.map_id, Category.id_comp, Iso.hom_inv_id_assoc]

private theorem unit_calculation
    {I S C D : Type*} [Category* I] [Category* S] [Category* C] [Category* D]
    (G : I ⥤ D) (F : S ⥤ D) (R : C ⥤ D)
    {A B C' : I} {E O V W : C} {J K L : S}
    (eta : A ⟶ B) (u : B ⟶ C') (kappa : G.obj C' ⟶ R.obj E) (ell : E ⟶ O)
    (d : G.obj B ⟶ R.obj V) (g : G.obj A ⟶ F.obj J) (k : J ⟶ K)
    (eps : F.obj K ⟶ R.obj V) (s : V ⟶ W) (m : K ⟶ L)
    (eps' : F.obj L ⟶ R.obj W) (t : W ⟶ O)
    (hp : G.map u ≫ (kappa ≫ R.map ell) = d ≫ R.map (s ≫ t))
    (hu : G.map eta ≫ d = (g ≫ F.map k) ≫ eps)
    (he : F.map m ≫ eps' = eps ≫ R.map s) :
    G.map (eta ≫ u) ≫ (kappa ≫ R.map ell) =
      g ≫ F.map (k ≫ m) ≫ eps' ≫ R.map t := by
  have hU : G.map eta ≫ d = g ≫ F.map k ≫ eps :=
    hu.trans (Category.assoc _ _ _)
  simp only [Functor.map_comp, Category.assoc] at hp ⊢
  rw [hp, reassoc_of% hU, ← reassoc_of% he]

private theorem qh_map_quotient
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {A B : CochainComplex C ℤ} (a : A ⟶ B) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map a) =
      DerivedCategory.Q.map a := by
  have h := DerivedCategory.quotientCompQhIso_hom_naturality a
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map a) ≫
      𝟙 _ = 𝟙 _ ≫ DerivedCategory.Q.map a at h
  simpa only [Category.id_comp, Category.comp_id] using h

-- The concrete localization and total-comparison interfaces require extra elaboration steps.
/-- Explicit resolution conjugation identities, their naturality, and counit substitution.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E; the agent calculation
refining the representative square (auxiliary; not a blueprint node).

Proof:
1. Reverse the resolution-compatibility clause of sectionDerivedPushpullNormalization.
   This gives the unary equation at every internal complex.
2. The first clause of TensorRepresentativeCondition holds for every pair of internal
   complexes. Cancel the inverse localization and tensor-comparison factors to obtain
   the representative identity. Paste this with the unary equation at the total tensor,
   gamma-naturality at the internal representative map, and epsilon-naturality at the
   ordinary total comparison. The result is the binary input equation.
3. Apply the representative identity at the two internal pullbacks. Naturality of
   qTensor at the termwise pullback comparisons, naturality of tensorComparison at the
   two eta maps, and the two unary equations give the output equation. Bifunctoriality
   combines the paired transports. No resolving-preservation hypothesis is needed here.
4. Cancel the invertible source transports in the ordinary total-comparison clause of
   section_oplax_total_comparison. Localize and paste with kappa-naturality. For units,
   cancel the corresponding ordinary unit transports, then apply kappa-naturality,
   the unary equation at the internal unit, and epsilon-naturality at its comparison.
5. The pure-tensor characterization identifies ordinaryTensorComparison with the
   natural comparison of internal_section_tensor_comparison. Its summand formula and
   coproduct extensionality prove naturality of totalComparison. Naturality of eta,
   kappa, the termwise pullback comparison and the actual total oplax map then gives
   all four Naturality squares.
6. Use epsilon-, qTensor- and section-total naturality to transport the equations along
   arbitrary section-complex isomorphisms. K-flatness is invariant under tensoring such
   an isomorphism, and termwise flatness is invariant under the induced isomorphism of
   tensor-right functors. Apply the resolving equivalence to the termwise inverse
   image and its counit. Epsilon-naturality and inverse cancellation give the final
   unit substitution. All the displayed maps remain the specified comparisons.
-/
theorem section_resolution_conjugation_identities {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ (A B : CochainComplex (internalModules Λ Y) ℤ),
      KFlatSectionComparison.internalResolving Λ Y A →
      KFlatSectionComparison.internalResolving Λ Y B → Equations Λ f A B) ∧
    UnitEquation Λ f ∧ Naturality Λ f ∧
    (∀ (P Q : CochainComplex (modules Λ Y) ℤ),
      KFlatSectionComparison.sectionResolving Λ Y P →
      KFlatSectionComparison.sectionResolving Λ Y Q →
      KFlatSectionComparison.internalResolving Λ Y
          (((equivalence Λ Y).mapHomologicalComplex (.up ℤ)).inverse.obj P) ∧
      KFlatSectionComparison.internalResolving Λ Y
          (((equivalence Λ Y).mapHomologicalComplex (.up ℤ)).inverse.obj Q) ∧
      SubstitutionEquations Λ f
        (((equivalence Λ Y).mapHomologicalComplex (.up ℤ)).inverse.obj P)
        (((equivalence Λ Y).mapHomologicalComplex (.up ℤ)).inverse.obj Q) P Q
        (((equivalence Λ Y).mapHomologicalComplex (.up ℤ)).counitIso.app P)
        (((equivalence Λ Y).mapHomologicalComplex (.up ℤ)).counitIso.app Q)) ∧
    UnitSubstitution Λ f
      ((totalSectionEquivalence Λ Y).obj
        (((equivalence Λ Y).mapHomologicalComplex (.up ℤ)).inverse.obj
          (𝟙_ (CochainComplex (modules Λ Y) ℤ))))
      (((equivalence Λ Y).mapHomologicalComplex (.up ℤ)).counitIso.app
        (𝟙_ (CochainComplex (modules Λ Y) ℤ))).symm := by
  have epsilon_naturality
      {P Q : CochainComplex (modules Λ Y) ℤ} (a : P ⟶ Q) :
      (derivedPullback Λ f).map (DerivedCategory.Q.map a) ≫ epsilon Λ f Q =
        epsilon Λ f P ≫ DerivedCategory.Q.map ((totalSectionPull Λ f).map a) := by
    have hn := (pullback Λ f).mapDerivedCategoryFactors.hom.naturality a
    simpa only [epsilon, derivedPullback, totalSectionPull, Functor.comp_map] using hn
  have kappa_naturality (T : Scheme.{u})
      {A B : CochainComplex (internalModules Λ T) ℤ} (a : A ⟶ B) :
      (derivedSectionFunctor Λ T).map ((internalLocalizationFunctor Λ T).map a) ≫
          (cochainLocalizationIso Λ T B).hom =
        (cochainLocalizationIso Λ T A).hom ≫
          DerivedCategory.Q.map ((totalSectionEquivalence Λ T).map a) := by
    exact cochainLocalizationIso_naturality Λ T a
  have unary_equation
      (A : CochainComplex (internalModules Λ Y) ℤ) :
      (derivedSectionFunctor Λ X).map (eta Λ f A) ≫ d Λ f A =
        j Λ f A ≫ epsilon Λ f ((totalSectionEquivalence Λ Y).obj A) := by
    have h := (sectionDerivedPushpullNormalization Λ f).2.2.2.2.1 A
    conv at h =>
      rhs
      lhs
      rw [_root_.counit_quotient_transport]
    with_unfolding_all
      unfold eta d j epsilon cochainLocalizationIso termwisePullComparison
      simp only [internalDerivedPullFunctor, internalLocalizationFunctor,
        totalInternalPull, retainedCochainFunctor, retainedCochainObject]
      exact reverse_assoc_square _ _ _ h
  have qTensor_naturality (T : Scheme.{u})
      {A A' B B' : CochainComplex (modules Λ T) ℤ} (a : A ⟶ A') (b : B ⟶ B') :
      (tensor Λ T).map (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) ≫
        qTensorArrow Λ T A' B' =
      qTensorArrow Λ T A B ≫ DerivedCategory.Q.map (a ⊗ₘ b) := by
    exact qTensorArrow_naturality Λ T a b
  have representative_equation (T : Scheme.{u})
      (A B : CochainComplex (internalModules Λ T) ℤ) :
      (derivedSectionFunctor Λ T).map
          (internalQTensorArrow Λ T A B) ≫
          (cochainLocalizationIso Λ T (A ⊗ B)).hom ≫
          DerivedCategory.Q.map (cochainTensorComparison Λ T A B).hom =
        (derivedSectionTensorIso Λ T ((internalLocalizationFunctor Λ T).obj A)
            ((internalLocalizationFunctor Λ T).obj B)).hom ≫
          (tensor Λ T).map (Prod.mkHom (cochainLocalizationIso Λ T A).hom
            (cochainLocalizationIso Λ T B).hom) ≫
          qTensorArrow Λ T ((totalSectionEquivalence Λ T).obj A)
            ((totalSectionEquivalence Λ T).obj B) := by
    exact qTensorArrow_normalization Λ T A B
  have input_equation
      (A B : CochainComplex (internalModules Λ Y) ℤ) :
      (derivedSectionFunctor Λ X).map (aInternal Λ f A B) ≫ dZ Λ f A B =
        jTensor Λ f A B ≫ aSection Λ f ((totalSectionEquivalence Λ Y).obj A)
          ((totalSectionEquivalence Λ Y).obj B) := by
    unfold aInternal dZ jTensor aSection
    apply input_calculation
      (derivedSectionFunctor Λ X) (internalDerivedPullFunctor Λ f)
      (derivedSectionFunctor Λ Y) (derivedPullback Λ f) (derivedPullSquare Λ f).hom
      (internalQTensorArrow Λ Y A B)
      (eta Λ f (A ⊗ B)) (d Λ f (A ⊗ B))
      (DerivedCategory.Q.map ((totalSectionPull Λ f).map (cochainTensorComparison Λ Y A B).hom))
      (cochainLocalizationIso Λ Y (A ⊗ B)).hom
      ((derivedSectionTensorIso Λ Y ((internalLocalizationFunctor Λ Y).obj A)
          ((internalLocalizationFunctor Λ Y).obj B)).hom ≫
        (tensor Λ Y).map (Prod.mkHom (cochainLocalizationIso Λ Y A).hom
          (cochainLocalizationIso Λ Y B).hom))
      (DerivedCategory.Q.map (cochainTensorComparison Λ Y A B).hom)
      (qTensorArrow Λ Y ((totalSectionEquivalence Λ Y).obj A) ((totalSectionEquivalence Λ Y).obj B))
      (epsilon Λ f ((totalSectionEquivalence Λ Y).obj (A ⊗ B)))
      (epsilon Λ f ((totalSectionEquivalence Λ Y).obj A ⊗
        (totalSectionEquivalence Λ Y).obj B))
    · have h := unary_equation (A ⊗ B)
      unfold j at h
      exact h.trans (Category.assoc _ _ _)
    · exact epsilon_naturality (cochainTensorComparison Λ Y A B).hom
    · exact (representative_equation Y A B).trans (Category.assoc _ _ _).symm
  have output_equation
      (A B : CochainComplex (internalModules Λ Y) ℤ) :
      (derivedSectionFunctor Λ X).map (cInternal Λ f A B) ≫ dOut Λ f A B =
        kTensor Λ f A B ≫ cSection Λ f ((totalSectionEquivalence Λ Y).obj A)
          ((totalSectionEquivalence Λ Y).obj B) := by
    unfold cInternal dOut kTensor cSection
    apply output_calculation (derivedSectionFunctor Λ X) (tensor Λ X)
      (fun M N ↦ (derivedSectionTensorIso Λ X M N).hom)
      (derivedSectionTensorIso_naturality Λ X) (eta Λ f A) (eta Λ f B)
      (internalQTensorArrow Λ X
        ((totalInternalPull Λ f).obj A) ((totalInternalPull Λ f).obj B))
      (cochainLocalizationIso Λ X
        ((totalInternalPull Λ f).obj A ⊗ (totalInternalPull Λ f).obj B)).hom
      (DerivedCategory.Q.map
        (cochainTensorComparison Λ X ((totalInternalPull Λ f).obj A)
          ((totalInternalPull Λ f).obj B)).hom)
      (DerivedCategory.Q.map
        ((termwisePullComparison Λ f A).hom ⊗ₘ (termwisePullComparison Λ f B).hom))
      (cochainLocalizationIso Λ X ((totalInternalPull Λ f).obj A)).hom
      (cochainLocalizationIso Λ X ((totalInternalPull Λ f).obj B)).hom
      (DerivedCategory.Q.map (termwisePullComparison Λ f A).hom)
      (DerivedCategory.Q.map (termwisePullComparison Λ f B).hom)
      (qTensorArrow Λ X
        ((totalSectionEquivalence Λ X).obj ((totalInternalPull Λ f).obj A))
        ((totalSectionEquivalence Λ X).obj ((totalInternalPull Λ f).obj B)))
      (qTensorArrow Λ X
        ((totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj A))
        ((totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj B)))
      ((derivedPullSquare Λ f).hom.app ((internalLocalizationFunctor Λ Y).obj A))
      ((derivedPullSquare Λ f).hom.app ((internalLocalizationFunctor Λ Y).obj B))
      ((derivedPullback Λ f).map (cochainLocalizationIso Λ Y A).hom)
      ((derivedPullback Λ f).map (cochainLocalizationIso Λ Y B).hom)
      (epsilon Λ f ((totalSectionEquivalence Λ Y).obj A))
      (epsilon Λ f ((totalSectionEquivalence Λ Y).obj B))
    · exact representative_equation X
        ((totalInternalPull Λ f).obj A) ((totalInternalPull Λ f).obj B)
    · exact qTensor_naturality X
        (termwisePullComparison Λ f A).hom (termwisePullComparison Λ f B).hom
    · have h := unary_equation A
      unfold d j at h
      exact h.trans (Category.assoc _ _ _)
    · have h := unary_equation B
      unfold d j at h
      exact h.trans (Category.assoc _ _ _)
  have total_equation
      (A B : CochainComplex (internalModules Λ Y) ℤ) :
      (derivedSectionFunctor Λ X).map
          ((internalLocalizationFunctor Λ X).map (actualInternalTotalIso Λ f A B).hom) ≫ dOut Λ
              f A B =
        dZ Λ f A B ≫ DerivedCategory.Q.map
          (sectionTotalIso Λ f ((totalSectionEquivalence Λ Y).obj A)
            ((totalSectionEquivalence Λ Y).obj B)).hom := by
    have hc := undo_explicit_conjugation
      (totalSectionPull Λ f) (totalSectionEquivalence Λ X)
      (cochainTensorComparison Λ Y A B)
      (termwisePullComparison Λ f (A ⊗ B))
      (actualInternalTotalIso Λ f A B)
      (cochainTensorComparison Λ X ((totalInternalPull Λ f).obj A)
        ((totalInternalPull Λ f).obj B))
      (tensorIso (termwisePullComparison Λ f A) (termwisePullComparison Λ f B))
      (sectionTotalIso Λ f ((totalSectionEquivalence Λ Y).obj A)
        ((totalSectionEquivalence Λ Y).obj B)).hom
      (by
        simpa only [conjugatedInternalTotalIso, totalTensorComparison,
          sectionConjugationIso, tensorIso_hom] using
          ((section_oplax_total_comparison Λ f).1 A B).1)
    dsimp only [tensorIso_hom] at hc
    unfold dOut dZ d
    exact paste_mapped_triple DerivedCategory.Q
      (kappa_naturality X (actualInternalTotalIso Λ f A B).hom) hc
  have unit_equation :
      UnitEquation Λ f := by
    have hc := cochainPullUnitCompatibility Λ f
    have hp := paste (kappa_naturality X (internalPullUnitArrow Λ f))
      (map_square DerivedCategory.Q hc)
    have hu := unary_equation (internalCochainUnit Λ Y)
    have he := epsilon_naturality (cochainUnitComparison Λ Y).hom
    have h := unit_calculation
      (derivedSectionFunctor Λ X) (derivedPullback Λ f) DerivedCategory.Q
      (eta Λ f (internalCochainUnit Λ Y))
      ((internalLocalizationFunctor Λ X).map (internalPullUnitArrow Λ f))
      (cochainLocalizationIso Λ X (internalCochainUnit Λ X)).hom
      (cochainUnitComparison Λ X).hom
      (d Λ f (internalCochainUnit Λ Y))
      ((derivedPullSquare Λ f).hom.app
        ((internalLocalizationFunctor Λ Y).obj (internalCochainUnit Λ Y)))
      (cochainLocalizationIso Λ Y (internalCochainUnit Λ Y)).hom
      (epsilon Λ f ((totalSectionEquivalence Λ Y).obj
        (internalCochainUnit Λ Y)))
      ((totalSectionPull Λ f).map (cochainUnitComparison Λ Y).hom)
      (DerivedCategory.Q.map (cochainUnitComparison Λ Y).hom)
      (epsilon Λ f (sectionCochainUnit Λ Y))
      (sectionPullUnitArrow Λ f)
      (by unfold d; exact hp)
      (by with_unfolding_all exact hu) he
    unfold UnitEquation e
    exact h
  have total_naturality (T : Scheme.{u})
      {A A' B B' : CochainComplex (internalModules Λ T) ℤ} (a : A ⟶ A') (b : B ⟶ B') :
      (totalSectionEquivalence Λ T).map (a ⊗ₘ b) ≫ (cochainTensorComparison Λ T A' B').hom =
        (cochainTensorComparison Λ T A B).hom ≫
          ((totalSectionEquivalence Λ T).map a ⊗ₘ (totalSectionEquivalence Λ T).map b) := by
    exact cochainTensorComparison_naturality Λ T a b
  have termwisePull_naturality
      {A B : CochainComplex (internalModules Λ Y) ℤ} (a : A ⟶ B) :
      (totalSectionEquivalence Λ X).map ((totalInternalPull Λ f).map a) ≫
          (termwisePullComparison Λ f B).hom =
        (termwisePullComparison Λ f A).hom ≫
          (totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map a) := by
    exact termwisePullComparison_naturality Λ f a
  have d_naturality
      {A B : CochainComplex (internalModules Λ Y) ℤ} (a : A ⟶ B) :
      (derivedSectionFunctor Λ X).map
          ((internalLocalizationFunctor Λ X).map ((totalInternalPull Λ f).map a)) ≫ d Λ f B =
        d Λ f A ≫ DerivedCategory.Q.map
          ((totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map a)) := by
    unfold d
    exact paste (kappa_naturality X ((totalInternalPull Λ f).map a))
      (map_square DerivedCategory.Q (termwisePull_naturality a))
  have dZ_naturality
      {A A' B B' : CochainComplex (internalModules Λ Y) ℤ} (a : A ⟶ A') (b : B ⟶ B') :
      (derivedSectionFunctor Λ X).map
          ((internalLocalizationFunctor Λ X).map ((totalInternalPull Λ f).map (a ⊗ₘ b))) ≫ dZ Λ
              f A' B' =
        dZ Λ f A B ≫ DerivedCategory.Q.map ((totalSectionPull Λ f).map
          ((totalSectionEquivalence Λ Y).map a ⊗ₘ (totalSectionEquivalence Λ Y).map b)) := by
    unfold dZ
    exact paste (d_naturality (a ⊗ₘ b))
      (map_square (totalSectionPull Λ f ⋙ DerivedCategory.Q) (total_naturality Y a b))
  have dOut_naturality
      {A A' B B' : CochainComplex (internalModules Λ Y) ℤ} (a : A ⟶ A') (b : B ⟶ B') :
      (derivedSectionFunctor Λ X).map ((internalLocalizationFunctor Λ X).map
          ((totalInternalPull Λ f).map a ⊗ₘ (totalInternalPull Λ f).map b)) ≫ dOut Λ f A' B' =
        dOut Λ f A B ≫ DerivedCategory.Q.map
          ((totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map a) ⊗ₘ
            (totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map b)) := by
    have hh := tensor_square (termwisePull_naturality a) (termwisePull_naturality b)
    unfold dOut
    exact paste (kappa_naturality X
      ((totalInternalPull Λ f).map a ⊗ₘ (totalInternalPull Λ f).map b))
        (paste (map_square DerivedCategory.Q
          (total_naturality X ((totalInternalPull Λ f).map a)
            ((totalInternalPull Λ f).map b))) (map_square DerivedCategory.Q hh))
  have eta_naturality
      {A B : CochainComplex (internalModules Λ Y) ℤ} (a : A ⟶ B) :
      (internalDerivedPullFunctor Λ f).map ((internalLocalizationFunctor Λ Y).map a) ≫ eta Λ f B =
        eta Λ f A ≫ (internalLocalizationFunctor Λ X).map ((totalInternalPull Λ f).map a) := by
    have h := (CondensedRing.upperStar Λ f).leftDerivedFunctorCounit.naturality
      ((HomotopyCategory.quotient _ (.up ℤ)).map a)
    with_unfolding_all
      simp only [eta, internalDerivedPullFunctor, internalLocalizationFunctor,
        totalInternalPull, retainedCochainFunctor, retainedCochainObject,
        retainedCochainMap, Functor.comp_map,
        Functor.mapHomotopyCategory_map, qh_map_quotient] at h ⊢
      exact h
  have aInternal_naturality
      {A A' B B' : CochainComplex (internalModules Λ Y) ℤ} (a : A ⟶ A') (b : B ⟶ B') :
      (internalDerivedPullFunctor Λ f).map ((internalLocalizationFunctor Λ Y).map a ⊗ₘ
          (internalLocalizationFunctor Λ Y).map b) ≫
          aInternal Λ f A' B' =
        aInternal Λ f A B ≫ (internalLocalizationFunctor Λ X).map ((totalInternalPull Λ f).map
            (a ⊗ₘ b)) := by
    unfold aInternal
    exact paste
      (map_square (internalDerivedPullFunctor Λ f) (internalQTensorArrow_naturality Λ Y a b))
      (eta_naturality (a ⊗ₘ b))
  have cInternal_naturality
      {A A' B B' : CochainComplex (internalModules Λ Y) ℤ} (a : A ⟶ A') (b : B ⟶ B') :
      ((internalDerivedPullFunctor Λ f).map ((internalLocalizationFunctor Λ Y).map a) ⊗ₘ
          (internalDerivedPullFunctor Λ f).map ((internalLocalizationFunctor Λ Y).map b)) ≫
              cInternal Λ f A' B' =
        cInternal Λ f A B ≫ (internalLocalizationFunctor Λ X).map
          ((totalInternalPull Λ f).map a ⊗ₘ (totalInternalPull Λ f).map b) := by
    unfold cInternal
    have hh := map_square (Functor.uncurry.obj (CondensedRing.derivedTensor Λ X))
      (pair_square (eta_naturality a) (eta_naturality b))
    exact paste hh
      (internalQTensorArrow_naturality Λ X
        ((totalInternalPull Λ f).map a) ((totalInternalPull Λ f).map b))
  have actualTotal_naturality
      {A A' B B' : CochainComplex (internalModules Λ Y) ℤ} (a : A ⟶ A') (b : B ⟶ B') :
      (totalInternalPull Λ f).map (a ⊗ₘ b) ≫ (actualInternalTotalIso Λ f A' B').hom =
        (actualInternalTotalIso Λ f A B).hom ≫
          ((totalInternalPull Λ f).map a ⊗ₘ (totalInternalPull Λ f).map b) := by
    exact actualInternalTotalIso_naturality Λ f a b
  have naturality : Naturality Λ f := by
    unfold Naturality
    intro A B A' B' hA hB hA' hB' a b
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact paste_right (map_square (derivedSectionFunctor Λ X) (eta_naturality a))
        (d_naturality a)
    · exact paste_right
        (map_square (derivedSectionFunctor Λ X) (aInternal_naturality a b))
        (dZ_naturality a b)
    · exact paste_right
        (map_square (derivedSectionFunctor Λ X) (cInternal_naturality a b))
        (dOut_naturality a b)
    · exact paste_right
        (map_square ((internalLocalizationFunctor Λ X) ⋙ (derivedSectionFunctor Λ X))
          (actualTotal_naturality a b)) (dOut_naturality a b)
  have aSection_naturality
      {P P' Q Q' : CochainComplex (modules Λ Y) ℤ} (a : P ⟶ P') (b : Q ⟶ Q') :
      (derivedPullback Λ f).map
          ((tensor Λ Y).map (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b))) ≫
          aSection Λ f P' Q' =
        aSection Λ f P Q ≫ DerivedCategory.Q.map ((totalSectionPull Λ f).map (a ⊗ₘ b)) := by
    unfold aSection
    exact paste (map_square (derivedPullback Λ f) (qTensor_naturality Y a b))
      (epsilon_naturality (a ⊗ₘ b))
  have cSection_naturality
      {P P' Q Q' : CochainComplex (modules Λ Y) ℤ} (a : P ⟶ P') (b : Q ⟶ Q') :
      (tensor Λ X).map (Prod.mkHom
          ((derivedPullback Λ f).map (DerivedCategory.Q.map a))
          ((derivedPullback Λ f).map (DerivedCategory.Q.map b))) ≫ cSection Λ f P' Q' =
        cSection Λ f P Q ≫ DerivedCategory.Q.map
          ((totalSectionPull Λ f).map a ⊗ₘ (totalSectionPull Λ f).map b) := by
    unfold cSection
    exact paste
      (map_square (tensor Λ X) (pair_square (epsilon_naturality a) (epsilon_naturality b)))
      (qTensor_naturality X ((totalSectionPull Λ f).map a) ((totalSectionPull Λ f).map b))
  have sectionTotal_naturality
      {P P' Q Q' : CochainComplex (modules Λ Y) ℤ} (a : P ⟶ P') (b : Q ⟶ Q') :
      DerivedCategory.Q.map ((totalSectionPull Λ f).map (a ⊗ₘ b)) ≫
          DerivedCategory.Q.map (sectionTotalIso Λ f P' Q').hom =
        DerivedCategory.Q.map (sectionTotalIso Λ f P Q).hom ≫ DerivedCategory.Q.map
          ((totalSectionPull Λ f).map a ⊗ₘ (totalSectionPull Λ f).map b) := by
    exact map_square DerivedCategory.Q
      (((section_oplax_total_comparison Λ f).2.2.2.2.2.2.2.2.1 P Q P' Q' a b).1)
  have substitution
      (A B : CochainComplex (internalModules Λ Y) ℤ)
      (P Q : CochainComplex (modules Λ Y) ℤ)
      (σ : (totalSectionEquivalence Λ Y).obj A ≅ P)
      (τ : (totalSectionEquivalence Λ Y).obj B ≅ Q) (h : Equations Λ f A B) :
      SubstitutionEquations Λ f A B P Q σ τ := by
    unfold Equations at h
    unfold SubstitutionEquations
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact substitute_square h.1 (epsilon_naturality σ.hom)
    · exact substitute_square h.2.1 (aSection_naturality σ.hom τ.hom)
    · exact substitute_square h.2.2.1 (cSection_naturality σ.hom τ.hom)
    · exact substitute_square h.2.2.2 (sectionTotal_naturality σ.hom τ.hom)
  have unit_substitution
      (P : CochainComplex (modules Λ Y) ℤ)
      (σ : sectionCochainUnit Λ Y ≅ P) : UnitSubstitution Λ f P σ := by
    have h := unit_equation
    unfold UnitEquation at h
    unfold UnitSubstitution
    exact h.trans (unit_iso_transport (derivedPullback Λ f) DerivedCategory.Q
      (totalSectionPull Λ f) DerivedCategory.Q
      ((derivedPullSquare Λ f).hom.app
        ((internalLocalizationFunctor Λ Y).obj (internalCochainUnit Λ Y)))
      (e Λ Y) σ (epsilon Λ f _) (epsilon Λ f P) (sectionPullUnitArrow Λ f)
      (epsilon_naturality σ.hom))
  have sectionResolving_of_iso (T : Scheme.{u})
      {P Q : CochainComplex (modules Λ T) ℤ} (σ : P ≅ Q)
      (h : KFlatSectionComparison.sectionResolving Λ T P) :
      KFlatSectionComparison.sectionResolving Λ T Q := by
    refine ⟨?_, ?_⟩
    · intro Z hZ n
      exact (h.1 Z hZ n).of_iso
        (((curriedTensor (modules Λ T)).map₂CochainComplex.obj Z).mapIso σ)
    · intro n
      exact (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso (ring Λ T) (P.X n) ≪≫
          (curriedTensor (modules Λ T)).flip.mapIso
            ((HomologicalComplex.eval _ _ n).mapIso σ) ≪≫
          (SheafOfModules.siteSheafTensorRightIso (ring Λ T) (Q.X n)).symm) (h.2 n)
  have inverse_resolving (T : Scheme.{u})
      (P : CochainComplex (modules Λ T) ℤ)
      (hP : KFlatSectionComparison.sectionResolving Λ T P) :
      KFlatSectionComparison.internalResolving Λ T
        (((equivalence Λ T).mapHomologicalComplex (.up ℤ)).inverse.obj P) := by
    apply ((KFlatSectionComparison.section_kflat_tensor_comparison.{u, u + 1, u + 1}
      Λ T).2.1 _).mpr
    exact sectionResolving_of_iso T
      (((equivalence Λ T).mapHomologicalComplex (.up ℤ)).counitIso.app P).symm hP
  have hEq (A B : CochainComplex (internalModules Λ Y) ℤ) : Equations Λ f A B := by
    unfold Equations
    exact ⟨unary_equation A, input_equation A B,
      output_equation A B, total_equation A B⟩
  refine ⟨fun A B _ _ ↦ hEq A B, unit_equation, naturality, ?_, ?_⟩
  · intro P Q hP hQ
    exact ⟨inverse_resolving Y P hP, inverse_resolving Y Q hQ,
      substitution _ _ P Q
        (((equivalence Λ Y).mapHomologicalComplex (.up ℤ)).counitIso.app P)
        (((equivalence Λ Y).mapHomologicalComplex (.up ℤ)).counitIso.app Q) (hEq _ _)⟩
  · with_unfolding_all exact unit_substitution _ _

end ResolutionConjugation
end AlgebraicGeometry.ProEtale.ModuleRingedComparison
