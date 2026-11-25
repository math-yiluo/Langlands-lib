/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Adjunction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.CategoryTheory.Roos.RoosComparisonHorizontalCoherenceSupplement
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Adjunction units and normalized signed Roos comparisons

Source: Stacks Project, Tag 0941, lemma-derived-limit-is-ok; Tags 09BN and 09BP;
blueprint prop-sf-pf-coherence, open-factor base-change paragraph
(blueprint: lem-sf-roos-adjunction-unit-coherence).

The record below bundles the specified comparisons together with their equations.
Its fields are conclusions, not extra assumptions of the theorem. The underlying Roos
functor is the existing shifted cone. The signed coordinates put the unshifted product
first, with differential (dx,(1-s)x-dy). The same normalized theta is used for both
functors; every augmentation is an actual chain map with zero second coordinate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe uA vA uB vB wA wB uC vC r uD vD s

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RoosAdjunctionUnit

/-- Localize the specified degreewise adjunction using the standard exact-functor
factorizations. Both units and counits are the localized original maps.
Source: Stacks Project, Tag 015F (blueprint: lem-sf-roos-adjunction-unit-coherence).
This helper extends the recorded construction to independent universes; its common-universe
specialization is identified by `exactDerivedAdjunctionUniverses_commonUniverses`. -/
def exactDerivedAdjunctionUniverses
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    F.mapDerivedCategory ⊣ G.mapDerivedCategory :=
  letI : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory := ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory

section Helpers
variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]

/-- Transparent termwise application on strict tower complexes.
Source: Stacks 0941 (blueprint: lem-sf-roos-adjunction-unit-coherence). -/
abbrev towerComplex (F : A ⥤ B) [F.Additive] :=
  ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)

/-- The standard exact localization of termwise application on strict towers.
Source: Stacks 0941 (blueprint: lem-sf-roos-adjunction-unit-coherence). -/
abbrev towerDerived [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :=
  @Functor.mapDerivedCategory _ _ _ _ _ _ _ _
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) inferInstance
    (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)

/-- The standard localization factorization for termwise tower application.
Source: Stacks 0941 (blueprint: lem-sf-roos-adjunction-unit-coherence). -/
abbrev towerFactors [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :=
  @Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) inferInstance
    (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)

/-- The specified exact derived adjunction on strict towers.
Source: Stacks 015F, 0941 (blueprint: lem-sf-roos-adjunction-unit-coherence). -/
def towerAdjunction [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    towerDerived F ⊣ towerDerived G :=
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  exactDerivedAdjunctionUniverses (a.whiskerRight ℕᵒᵖ)

/-- Signed coordinates (x,y)=(u,-v) on the existing shifted Roos cone.
Source: Stacks 0941; the signed normalization of exactProductFunctorStrictLimit
(blueprint: lem-sf-roos-adjunction-unit-coherence). -/
def coordinates [HasCountableProducts A] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosF.obj X).X (p + 1) ≅ (roosP X).X (p + 1) ⊞ (roosP X).X p :=
  roosχ X p ≪≫ biprod.braiding _ _ ≪≫
    biprod.mapIso (Iso.refl _) {
      hom := -𝟙 _
      inv := -𝟙 _
      hom_inv_id := by simp
      inv_hom_id := by simp }

end Helpers

section Statement
variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasLimits A] [HasLimits B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
  (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G)
  (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
  (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
  (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
    DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
  (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
    DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB)

/-- The comparisons and all conclusions of the adjunction-unit calculation, in one
record. In particular, kappa is specified on both signed product coordinates; theta
is natural and has the ordinary-limit inclusion normalization on K-injectives; lambda
is exactly its conjugate of kappa. No cone filler or arbitrary comparison is an input.
Source: Stacks 0941, 09BN, 09BP and the open-factor calculation in prop-sf-pf-coherence
(blueprint: lem-sf-roos-adjunction-unit-coherence). -/
structure Coherence where
  thetaA : DerivedCategory.Q ⋙ LA ≅ roosF ⋙ DerivedCategory.Q
  thetaB : DerivedCategory.Q ⋙ LB ≅ roosF ⋙ DerivedCategory.Q
  normalizationA : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective],
    (∀ p : ℤ, Injective (I.X p)) →
    etaA.app I ≫ thetaA.hom.app I = DerivedCategory.Q.map (roosι I)
  normalizationB : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [I.IsKInjective],
    (∀ p : ℤ, Injective (I.X p)) →
    etaB.app I ≫ thetaB.hom.app I = DerivedCategory.Q.map (roosι I)
  kappaF : roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅ towerComplex F ⋙ roosF
  kappaG : roosF ⋙ G.mapHomologicalComplex (.up ℤ) ≅ towerComplex G ⋙ roosF
  kappaF_coordinates : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ),
    (kappaF.hom.app X).f (p + 1) ≫ (coordinates ((towerComplex F).obj X) p).hom =
      F.map (coordinates X p).hom ≫
        F.biprodComparison ((roosP X).X (p + 1)) ((roosP X).X p) ≫
        biprod.map
          ((piComparison (F.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ X.asFunctor.obj (op n))).f (p + 1))
          ((piComparison (F.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ X.asFunctor.obj (op n))).f p)
  kappaG_coordinates : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ),
    (kappaG.hom.app X).f (p + 1) ≫ (coordinates ((towerComplex G).obj X) p).hom =
      G.map (coordinates X p).hom ≫
        G.biprodComparison ((roosP X).X (p + 1)) ((roosP X).X p) ≫
        biprod.map
          ((piComparison (G.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ X.asFunctor.obj (op n))).f (p + 1))
          ((piComparison (G.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ X.asFunctor.obj (op n))).f p)
  lambdaF : LA ⋙ F.mapDerivedCategory ≅ towerDerived F ⋙ LB
  lambdaG : LB ⋙ G.mapDerivedCategory ≅ towerDerived G ⋙ LA
  lambdaF_normalization : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    F.mapDerivedCategory.map (thetaA.hom.app X) ≫
        F.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
        DerivedCategory.Q.map (kappaF.hom.app X) =
      lambdaF.hom.app (DerivedCategory.Q.obj X) ≫
        LB.map ((towerFactors F).hom.app X) ≫ thetaB.hom.app ((towerComplex F).obj X)
  lambdaG_normalization : ∀ X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
    G.mapDerivedCategory.map (thetaB.hom.app X) ≫
        G.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
        DerivedCategory.Q.map (kappaG.hom.app X) =
      lambdaG.hom.app (DerivedCategory.Q.obj X) ≫
        LA.map ((towerFactors G).hom.app X) ≫ thetaA.hom.app ((towerComplex G).obj X)
  product_unit : ∀ M : ℕ → A,
    a.unit.app (∏ᶜ M) ≫ G.map (piComparison F M) ≫
        piComparison G (fun n : ℕ ↦ F.obj (M n)) =
      Limits.Pi.map (fun n : ℕ ↦ a.unit.app (M n))
  chain_unit : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    (a.mapHomologicalComplex (.up ℤ)).unit.app (roosF.obj X) ≫
        (G.mapHomologicalComplex (.up ℤ)).map (kappaF.hom.app X) ≫
        kappaG.hom.app ((towerComplex F).obj X) =
      roosF.map (((a.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).unit.app X)
  towerUnit : 𝟭 (DerivedCategory.{wA} (ℕᵒᵖ ⥤ A)) ≅ towerDerived F ⋙ towerDerived G
  towerUnit_hom : towerUnit.hom = (towerAdjunction a).unit
  derived_unit : ∀ M : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A),
    (exactDerivedAdjunctionUniverses a).unit.app (LA.obj M) ≫
        G.mapDerivedCategory.map (lambdaF.hom.app M) ≫
        lambdaG.hom.app ((towerDerived F).obj M) ≫ LA.map (towerUnit.inv.app M) =
      𝟙 (LA.obj M)
  augmentation : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (P : CochainComplex A ℤ)
    (gamma : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n)),
    (∀ n : ℕ, gamma (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n) →
    ∃ (b : P ⟶ roosF.obj X)
      (bGF : (G.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P) ⟶
        roosF.obj ((towerComplex G).obj ((towerComplex F).obj X))),
      (∀ p : ℤ, b.f (p + 1) ≫ (coordinates X p).hom =
        biprod.lift ((Pi.lift gamma).f (p + 1)) 0) ∧
      (∀ p : ℤ, bGF.f (p + 1) ≫
        (coordinates ((towerComplex G).obj ((towerComplex F).obj X)) p).hom =
        biprod.lift ((Pi.lift (fun n : ℕ ↦
          (G.mapHomologicalComplex (.up ℤ)).map
            ((F.mapHomologicalComplex (.up ℤ)).map (gamma n)))).f (p + 1)) 0) ∧
      b ≫ (a.mapHomologicalComplex (.up ℤ)).unit.app (roosF.obj X) ≫
          (G.mapHomologicalComplex (.up ℤ)).map (kappaF.hom.app X) ≫
          kappaG.hom.app ((towerComplex F).obj X) =
        (a.mapHomologicalComplex (.up ℤ)).unit.app P ≫ bGF ∧
      (∀ p : ℤ,
        (b ≫ (a.mapHomologicalComplex (.up ℤ)).unit.app (roosF.obj X) ≫
          (G.mapHomologicalComplex (.up ℤ)).map (kappaF.hom.app X) ≫
          kappaG.hom.app ((towerComplex F).obj X)).f (p + 1) ≫
            (coordinates ((towerComplex G).obj ((towerComplex F).obj X)) p).hom =
        biprod.lift ((Pi.lift (fun n : ℕ ↦ gamma n ≫
          (a.mapHomologicalComplex (.up ℤ)).unit.app (X.asFunctor.obj (op n)))).f (p + 1)) 0) ∧
      (exactDerivedAdjunctionUniverses a).unit.app (DerivedCategory.Q.obj P) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategory.map
            (DerivedCategory.Q.map b ≫ thetaA.inv.app X)) ≫
          G.mapDerivedCategory.map (lambdaF.hom.app (DerivedCategory.Q.obj X)) ≫
          lambdaG.hom.app ((towerDerived F).obj (DerivedCategory.Q.obj X)) ≫
          LA.map (towerUnit.inv.app (DerivedCategory.Q.obj X)) =
        DerivedCategory.Q.map b ≫ thetaA.inv.app X

end Statement

section ProofHelpers
variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]

omit [Abelian A] [Abelian B] in
private theorem preservesProducts (F : A ⥤ B)
    (h : ∀ M : ℕ → A, IsIso (piComparison F M)) :
    PreservesLimitsOfShape (Discrete ℕ) F where
  preservesLimit {K} := by
    have := h (fun n ↦ K.obj ⟨n⟩)
    have : PreservesLimit (Discrete.functor (K.obj ∘ Discrete.mk)) F :=
      PreservesProduct.of_iso_comparison F (K.obj ∘ Discrete.mk)
    exact preservesLimit_of_iso_diagram F Discrete.natIsoFunctor.symm

private def canonicalKappa (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F] :
    roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅ towerComplex F ⋙ roosF :=
  NatIso.ofComponents (fun X ↦ by
    have := roosAdditiveComparison_isIso F X
    exact (asIso (roosAdditiveComparison F X) :
      (roosF ⋙ F.mapHomologicalComplex (.up ℤ)).obj X ≅
        (towerComplex F ⋙ roosF).obj X))
    (fun f ↦ by
      simpa only [Functor.comp_map, asIso_hom, roosTowerAction] using
        roosAdditiveComparison_natural F f)

omit [HasCountableProducts A] [HasCountableProducts B] in
private theorem signedComparison (F : A ⥤ B) [F.Additive]
    {V P Q : A} {P' Q' : B} (c : V ⟶ P ⊞ Q)
    (f : F.obj P ⟶ P') (g : F.obj Q ⟶ Q') :
    (F.map c ≫ F.biprodComparison P Q ≫ biprod.map f g) ≫
        (biprod.braiding _ _).hom ≫ biprod.map (𝟙 _) (-𝟙 _) =
      F.map (c ≫ (biprod.braiding _ _).hom ≫ biprod.map (𝟙 _) (-𝟙 _)) ≫
        F.biprodComparison Q P ≫ biprod.map g f := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, Category.comp_id,
      biprod.braiding_hom, biprod.lift_fst, biprod.map_snd,
      Functor.biprodComparison_fst_assoc, Functor.biprodComparison_snd_assoc]
    rw [← F.map_comp_assoc, ← F.map_comp_assoc]
    simp
  · simp only [Category.assoc, biprod.map_snd, Preadditive.comp_neg,
      Category.comp_id, biprod.braiding_hom, biprod.lift_snd, biprod.map_fst,
      Functor.biprodComparison_fst_assoc, Functor.biprodComparison_snd_assoc]
    rw [← F.map_comp_assoc, ← F.map_comp_assoc]
    simp

private theorem chainUnit {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    (a : F ⊣ G) [IsIso a.unit]
    [PreservesLimitsOfShape (Discrete ℕ) F] [PreservesLimitsOfShape (Discrete ℕ) G]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (a.mapHomologicalComplex (.up ℤ)).unit.app (roosF.obj X) ≫
        (G.mapHomologicalComplex (.up ℤ)).map ((canonicalKappa F).hom.app X) ≫
        (canonicalKappa G).hom.app ((towerComplex F).obj X) =
      roosF.map (((a.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).unit.app X) := by
  let u := ((a.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).unit.app X
  let v := (NatTrans.mapHomologicalComplex
    ((Functor.whiskeringRight ℕᵒᵖ A A).map (asIso a.unit).inv) (.up ℤ)).app X
  have hvu : v ≫ u = 𝟙 _ := by
    ext i n
    simp [u, v, Adjunction.whiskerRight_unit_app_app]
  have h := roosComparison_horizontal_coherence F G (𝟭 A) (asIso a.unit).inv X
  rw [roosAdditiveComparison_id] at h
  change (G.mapHomologicalComplex (.up ℤ)).map (roosAdditiveComparison F X) ≫
    roosAdditiveComparison G ((towerComplex F).obj X) ≫ roosF.map v =
    (NatTrans.mapHomologicalComplex (asIso a.unit).inv (.up ℤ)).app
      (roosF.obj X) ≫ (𝟙 _ ≫ roosF.map (𝟙 X)) at h
  have hh := congrArg (fun z ↦
    (a.mapHomologicalComplex (.up ℤ)).unit.app (roosF.obj X) ≫ z ≫ roosF.map u) h
  have hc : (a.mapHomologicalComplex (.up ℤ)).unit.app (roosF.obj X) ≫
      (NatTrans.mapHomologicalComplex (asIso a.unit).inv (.up ℤ)).app (roosF.obj X) =
      𝟙 _ := by
    ext i
    change a.unit.app _ ≫ (asIso a.unit).inv.app _ = 𝟙 _
    exact (asIso a.unit).hom_inv_id_app _
  simp only [Category.assoc] at hh
  rw [← roosF.map_comp v u, hvu, roosF.map_id] at hh
  simp only [← Category.assoc, hc, roosF.map_id] at hh
  erw [Category.comp_id] at hh
  simpa only [canonicalKappa, NatIso.ofComponents_hom_app, asIso_hom, towerComplex,
    u, Functor.comp_obj, Functor.id_obj, Category.assoc,
    Category.comp_id, Category.id_comp] using hh

private theorem descendComparison
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (thetaA : DerivedCategory.Q ⋙ LA ≅ roosF ⋙ DerivedCategory.Q)
    (thetaB : DerivedCategory.Q ⋙ LB ≅ roosF ⋙ DerivedCategory.Q)
    (kappa : roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅ towerComplex F ⋙ roosF) :
    ∃ lambda : LA ⋙ F.mapDerivedCategory ≅ towerDerived F ⋙ LB,
      ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        F.mapDerivedCategory.map (thetaA.hom.app X) ≫
            F.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
            DerivedCategory.Q.map (kappa.hom.app X) =
          lambda.hom.app (DerivedCategory.Q.obj X) ≫
            LB.map ((towerFactors F).hom.app X) ≫
            thetaB.hom.app ((towerComplex F).obj X) := by
  let e₁ : DerivedCategory.Q ⋙ (LA ⋙ F.mapDerivedCategory) ≅
      roosF ⋙ (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight thetaA F.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft roosF F.mapDerivedCategoryFactors
  let e₂ : DerivedCategory.Q ⋙ (towerDerived F ⋙ LB) ≅
      towerComplex F ⋙ (roosF ⋙ DerivedCategory.Q) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (towerFactors F) LB ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (towerComplex F) thetaB
  let e := e₁ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight kappa DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫ e₂.symm
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) (DerivedCategory.{wB} B)
  let lambda := ff.preimageIso e
  have hl X : lambda.hom.app (DerivedCategory.Q.obj X) = e.hom.app X :=
    congr_app (ff.map_preimage e.hom) X
  refine ⟨lambda, fun X ↦ ?_⟩
  rw [hl X]
  have hh : e₁.hom.app X ≫ DerivedCategory.Q.map (kappa.hom.app X) =
      e.hom.app X ≫ e₂.hom.app X := by simp [e, Category.assoc]
  simpa only [e₁, e₂, Iso.trans_hom, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Category.id_comp, Category.comp_id, Category.assoc,
    Functor.map_id] using hh

end ProofHelpers

private theorem conjugateUnit {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) (G : B ⥤ A) (u : 𝟭 A ⟶ F ⋙ G)
    {P₀ H₀ P₂ H₂ : A} {P₁ H₁ : B}
    (t₀ : P₀ ⟶ H₀) (t₁ : P₁ ⟶ H₁) (t₂ : P₂ ⟶ H₂)
    (l₁ : F.obj P₀ ⟶ P₁) (l₂ : G.obj P₁ ⟶ P₂)
    (k₁ : F.obj H₀ ⟶ H₁) (k₂ : G.obj H₁ ⟶ H₂)
    (h₁ : F.map t₀ ≫ k₁ = l₁ ≫ t₁)
    (h₂ : G.map t₁ ≫ k₂ = l₂ ≫ t₂) :
    u.app P₀ ≫ G.map l₁ ≫ l₂ ≫ t₂ =
      t₀ ≫ u.app H₀ ≫ G.map k₁ ≫ k₂ := by
  rw [← h₂, ← G.map_comp_assoc, ← h₁, G.map_comp]
  have h := u.naturality t₀
  dsimp only [Functor.id_map, Functor.comp_map] at h
  rw [← Category.assoc, ← Category.assoc, ← h]
  simp only [Category.assoc]

section DerivedCalculation
variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesLimitsOfShape (Discrete ℕ) F] [PreservesLimitsOfShape (Discrete ℕ) G]

end DerivedCalculation

end CategoryTheory.RoosAdjunctionUnit
