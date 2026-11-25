/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RoosAdjunctionUnit.RoosAdjunctionUnitCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.CategoryTheory.Localization.Predicate
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosModel
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.CategoryTheory.Abelian.FunctorCategory
import all WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import all WeilConjectures.CategoryTheory.Roos.RoosComparisonHorizontalCoherenceSupplement

/-! # Normalized inverse-limit comparisons respect an exact functor square

Source: the final paragraph of
literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md;
projection and conjugation calculation in the DAG proof
(blueprint: lem-cbc-normalized-limit-square-coherence).

The records package conclusions of the theorem, rather than extra hypotheses.
The underlying complex is the existing `roosF`. Its existing signed `coordinates`
give (x,y) in degrees (q,q-1), with d(x,y)=(dx,(1-s)x-dy).
All comparisons use that same model at a shared corner.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option linter.all false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RoosAdjunctionUnit

namespace CategoryTheory.NormalizedLimitSquare

attribute [local irreducible] roosF roosχ roosι DerivedCategory.Q
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
attribute [local irreducible] roosAdditiveComparison coordinates

universe u v w u' v' w' u0 v0 w0 u1 v1 w1 u2 v2 w2 u3 v3 w3
universe c0 d0 r0 c1 d1 r1 c2 d2 r2 c3 d3 r3

/-- One corner's total derived limit and its fixed, K-injective-normalized Roos model.
`factors` identifies the localized Roos functor with the actual shifted cone.
Source: Stacks 0941 and the final blueprint comparison paragraph
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
structure Corner {A : Type u} [Category.{v} A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (L : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (eta : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ L) where
  roos : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A
  factors : DerivedCategory.Q ⋙ roos ≅ roosF ⋙ DerivedCategory.Q
  theta : L ≅ roos
  normalization : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective],
    (∀ q : ℤ, Injective (I.X q)) →
    eta.app I ≫ theta.hom.app (DerivedCategory.Q.obj I) ≫ factors.hom.app I =
      DerivedCategory.Q.map (roosι I)

section Edge
variable {A : Type u} [Category.{v} A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasCountableProducts B] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{w'} B] [HasDerivedCategory.{w'} (ℕᵒᵖ ⥤ B)]
  {LA : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A}
  {LB : DerivedCategory.{w'} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{w'} B}
  {etaA : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LA}
  {etaB : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LB}

/-- The specified comparison on one edge, including both signed coordinate equations,
its localization, and precisely lambda = theta inverse, kappa, F(theta).
Source: lem-cbc-exact-product-functor-strict-limit, signed Roos normalization
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
structure Comparison (a : Corner LA etaA) (b : Corner LB etaB)
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] where
  kappa : roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅ towerComplex F ⋙ roosF
  coordinate_formula : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ),
    (kappa.hom.app X).f (p + 1) ≫ (coordinates ((towerComplex F).obj X) p).hom =
      F.map (coordinates X p).hom ≫
        F.biprodComparison ((roosP X).X (p + 1)) ((roosP X).X p) ≫
        biprod.map ((piComparison (F.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ X.asFunctor.obj (op n))).f (p + 1))
          ((piComparison (F.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ X.asFunctor.obj (op n))).f p)
  derivedKappa : a.roos ⋙ F.mapDerivedCategory ≅ towerDerived F ⋙ b.roos
  descent : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    F.mapDerivedCategory.map (a.factors.hom.app X) ≫
        F.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
        DerivedCategory.Q.map (kappa.hom.app X) =
      derivedKappa.hom.app (DerivedCategory.Q.obj X) ≫
        b.roos.map ((towerFactors F).hom.app X) ≫
        b.factors.hom.app ((towerComplex F).obj X)
  lambda : LA ⋙ F.mapDerivedCategory ≅ towerDerived F ⋙ LB
  conjugation : ∀ M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A),
    lambda.hom.app M = F.mapDerivedCategory.map (a.theta.hom.app M) ≫
      derivedKappa.hom.app M ≫ b.theta.inv.app ((towerDerived F).obj M)

/-- The canonical derived augmentation obtained from the strict limit cone.
Source: the strict augmentation clause of Stacks 0941 and
(blueprint: lem-cbc-normalized-limit-square-coherence).
The named map keeps repeated limit-cone conversions out of the coherence record. -/
@[irreducible] def augmentation
    {T : ℕᵒᵖ ⥤ CochainComplex A ℤ} {Z : DerivedCategory.{w} A}
    (c : Cone T) (unit : DerivedCategory.Q.obj (limit T) ⟶ Z) :
    DerivedCategory.Q.obj c.pt ⟶ Z :=
  DerivedCategory.Q.map (limit.lift T c) ≫ unit

omit [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{w'} B] [HasDerivedCategory.{w'} (ℕᵒᵖ ⥤ B)]
  [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B] in
private theorem preservesProducts (F : A ⥤ B)
    (h : ∀ N : ℕ → A, IsIso (piComparison F N)) :
    PreservesLimitsOfShape (Discrete ℕ) F where
  preservesLimit {K} := by
    have := h (fun n ↦ K.obj ⟨n⟩)
    have : PreservesLimit (Discrete.functor (K.obj ∘ Discrete.mk)) F :=
      PreservesProduct.of_iso_comparison F (K.obj ∘ Discrete.mk)
    exact preservesLimit_of_iso_diagram F Discrete.natIsoFunctor.symm

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{w'} B] [HasDerivedCategory.{w'} (ℕᵒᵖ ⥤ B)] in
private theorem signedComparison (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosAdditiveComparison F X).f (p + 1) ≫
        (coordinates ((roosTowerAction F).obj X) p).hom =
      F.map (coordinates X p).hom ≫
        F.biprodComparison ((roosP X).X (p + 1)) ((roosP X).X p) ≫
        biprod.map ((roosProductComparison F X).f (p + 1))
          ((roosProductComparison F X).f p) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, Functor.biprodComparison_fst_assoc]
    rw [← F.map_comp_assoc]
    simpa [coordinates, Category.assoc] using comparison_snd F X p
  · simp only [Category.assoc, biprod.map_snd, Functor.biprodComparison_snd_assoc]
    rw [← F.map_comp_assoc]
    simpa [coordinates, Category.assoc] using congrArg Neg.neg (comparison_fst F X p)

private theorem liftComparison
    (a : Corner LA etaA) (b : Corner LB etaB)
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (k : roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅ towerComplex F ⋙ roosF) :
    ∃ d : a.roos ⋙ F.mapDerivedCategory ≅ towerDerived F ⋙ b.roos,
      ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      F.mapDerivedCategory.map (a.factors.hom.app X) ≫
        F.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
        DerivedCategory.Q.map (k.hom.app X) =
      d.hom.app (DerivedCategory.Q.obj X) ≫
        b.roos.map ((towerFactors F).hom.app X) ≫
        b.factors.hom.app ((towerComplex F).obj X) := by
  let s : DerivedCategory.Q ⋙ (a.roos ⋙ F.mapDerivedCategory) ≅
      (roosF ⋙ F.mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight a.factors F.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft roosF F.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm
  let t : DerivedCategory.Q ⋙ (towerDerived F ⋙ b.roos) ≅
      (towerComplex F ⋙ roosF) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (towerFactors F) b.roos ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (towerComplex F) b.factors ≪≫
      (Functor.associator _ _ _).symm
  let e := s ≪≫ Functor.isoWhiskerRight k DerivedCategory.Q ≪≫ t.symm
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) (DerivedCategory.{w'} B)
  let d := ff.preimageIso e
  refine ⟨d, ?_⟩
  intro X
  have h := congr_app (ff.map_preimage e.hom) X
  change d.hom.app (DerivedCategory.Q.obj X) = e.hom.app X at h
  have hh : s.hom.app X ≫ DerivedCategory.Q.map (k.hom.app X) =
      d.hom.app (DerivedCategory.Q.obj X) ≫ t.hom.app X := by
    rw [h]
    change s.hom.app X ≫ DerivedCategory.Q.map (k.hom.app X) =
      (s.hom.app X ≫ DerivedCategory.Q.map (k.hom.app X) ≫ t.inv.app X) ≫ t.hom.app X
    simp only [Category.assoc, Iso.inv_hom_id_app]
    dsimp only [Functor.comp_obj]
    rw [Category.comp_id]
  simpa only [s, t, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using hh

private theorem comparisonData (a : Corner LA etaA) (b : Corner LB etaB)
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hphi : ∀ N : ℕ → A, IsIso (piComparison F N)) :
    ∃ c : Comparison a b F, ∀ X, c.kappa.hom.app X = roosAdditiveComparison F X := by
  have : PreservesLimitsOfShape (Discrete ℕ) F := preservesProducts F hphi
  have (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : IsIso (roosAdditiveComparison F X) :=
    roosAdditiveComparison_isIso F X
  let k : roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅ towerComplex F ⋙ roosF :=
    NatIso.ofComponents (fun X ↦
      @asIso _ _ _ _ (roosAdditiveComparison F X) (roosAdditiveComparison_isIso F X))
      (fun f ↦ roosAdditiveComparison_natural F f)
  obtain ⟨d, hd⟩ := liftComparison a b F k
  let l : LA ⋙ F.mapDerivedCategory ≅ towerDerived F ⋙ LB :=
    Functor.isoWhiskerRight a.theta F.mapDerivedCategory ≪≫ d ≪≫
      Functor.isoWhiskerLeft (towerDerived F) b.theta.symm
  exact ⟨⟨k, (fun X p ↦ by exact signedComparison F X p), d, hd, l, fun _ ↦ rfl⟩, fun _ ↦ rfl⟩

private theorem comparison_normalization (a : Corner LA etaA) (b : Corner LB etaB)
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (c : Comparison a b F) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    c.lambda.hom.app (DerivedCategory.Q.obj X) ≫
        LB.map ((towerFactors F).hom.app X) ≫
        b.theta.hom.app (DerivedCategory.Q.obj ((towerComplex F).obj X)) ≫
        b.factors.hom.app ((towerComplex F).obj X) =
      F.mapDerivedCategory.map (a.theta.hom.app (DerivedCategory.Q.obj X) ≫
        a.factors.hom.app X) ≫ F.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
        DerivedCategory.Q.map (c.kappa.hom.app X) := by
  rw [c.conjugation, Functor.map_comp]
  simp only [Category.assoc]
  rw [← b.theta.inv.naturality_assoc]
  erw [Iso.inv_hom_id_app_assoc]
  rw [← c.descent]

private theorem path_descent
    {D : Type u3} [Category.{v3} D] [Abelian D]
    [HasCountableProducts D] [HasLimitsOfShape ℕᵒᵖ D]
    [HasDerivedCategory.{w3} D] [HasDerivedCategory.{w3} (ℕᵒᵖ ⥤ D)]
    {LD : DerivedCategory.{w3} (ℕᵒᵖ ⥤ D) ⥤ DerivedCategory.{w3} D}
    {etaD : roosLimitFunctor (A := D) ⋙ DerivedCategory.Q.{w3} (C := D) ⟶
      DerivedCategory.Q.{w3} (C := ℕᵒᵖ ⥤ D) ⋙ LD}
    (a : Corner LA etaA) (b : Corner LB etaB) (d : Corner LD etaD)
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : B ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (cF : Comparison a b F) (cG : Comparison b d G)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    G.mapDerivedCategory.map (cF.derivedKappa.hom.app (DerivedCategory.Q.obj X)) ≫
        cG.derivedKappa.hom.app ((towerDerived F).obj (DerivedCategory.Q.obj X)) ≫
        d.roos.map ((towerDerived G).map ((towerFactors F).hom.app X) ≫
          (towerFactors G).hom.app ((towerComplex F).obj X)) ≫
        d.factors.hom.app ((towerComplex G).obj ((towerComplex F).obj X)) =
      G.mapDerivedCategory.map (F.mapDerivedCategory.map (a.factors.hom.app X)) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app (roosF.obj X)) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj (roosF.obj X)) ≫
        DerivedCategory.Q.map
          ((G.mapHomologicalComplex (.up ℤ)).map (cF.kappa.hom.app X) ≫
            cG.kappa.hom.app ((towerComplex F).obj X)) := by
  simp only [Functor.map_comp, Category.assoc]
  erw [← cG.derivedKappa.hom.naturality_assoc]
  dsimp only [Functor.comp_map]
  erw [← cG.descent, ← G.mapDerivedCategory.map_comp_assoc,
    ← G.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  erw [← cF.descent]
  simp only [Functor.map_comp, Category.assoc]
  erw [G.mapDerivedCategoryFactors_hom_naturality_assoc]

end Edge

section Square
variable {A0 : Type u0} [Category.{v0} A0] [Abelian A0]
  [HasCountableProducts A0] [HasLimitsOfShape ℕᵒᵖ A0]
  [HasDerivedCategory.{w0} A0] [HasDerivedCategory.{w0} (ℕᵒᵖ ⥤ A0)]
variable {A1 : Type u1} [Category.{v1} A1] [Abelian A1]
  [HasCountableProducts A1] [HasLimitsOfShape ℕᵒᵖ A1]
  [HasDerivedCategory.{w1} A1] [HasDerivedCategory.{w1} (ℕᵒᵖ ⥤ A1)]
variable {A2 : Type u2} [Category.{v2} A2] [Abelian A2]
  [HasCountableProducts A2] [HasLimitsOfShape ℕᵒᵖ A2]
  [HasDerivedCategory.{w2} A2] [HasDerivedCategory.{w2} (ℕᵒᵖ ⥤ A2)]
variable {A3 : Type u3} [Category.{v3} A3] [Abelian A3]
  [HasCountableProducts A3] [HasLimitsOfShape ℕᵒᵖ A3]
  [HasDerivedCategory.{w3} A3] [HasDerivedCategory.{w3} (ℕᵒᵖ ⥤ A3)]
variable (F : A0 ⥤ A1) (G : A1 ⥤ A3) (H : A0 ⥤ A2) (K : A2 ⥤ A3)
  [F.Additive] [G.Additive] [H.Additive] [K.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K]

omit [HasCountableProducts A0] [HasCountableProducts A1]
  [HasCountableProducts A2] [HasCountableProducts A3]
  [HasLimitsOfShape ℕᵒᵖ A0] [HasLimitsOfShape ℕᵒᵖ A1]
  [HasLimitsOfShape ℕᵒᵖ A2] [HasLimitsOfShape ℕᵒᵖ A3]
  [HasDerivedCategory.{w0} A0] [HasDerivedCategory.{w1} A1]
  [HasDerivedCategory.{w2} A2] [HasDerivedCategory.{w3} A3]
  [HasDerivedCategory.{w0} (ℕᵒᵖ ⥤ A0)] [HasDerivedCategory.{w1} (ℕᵒᵖ ⥤ A1)]
  [HasDerivedCategory.{w2} (ℕᵒᵖ ⥤ A2)] [HasDerivedCategory.{w3} (ℕᵒᵖ ⥤ A3)]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K] in
/-- Termwise square map, with its two-step tower functors explicitly typed.
Source: naturality of the given square
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
@[irreducible] def towerMap (e : F ⋙ G ⟶ H ⋙ K) :
    towerComplex F ⋙ towerComplex G ⟶ towerComplex H ⋙ towerComplex K :=
  NatTrans.mapHomologicalComplex
    ((Functor.whiskeringRight ℕᵒᵖ A0 A3).map e) (.up ℤ)

omit [HasCountableProducts A0] [HasLimitsOfShape ℕᵒᵖ A0]
  [HasDerivedCategory.{w0} A0]
  [HasCountableProducts A1] [HasLimitsOfShape ℕᵒᵖ A1]
  [HasDerivedCategory.{w1} A1]
  [HasCountableProducts A2] [HasLimitsOfShape ℕᵒᵖ A2]
  [HasDerivedCategory.{w2} A2]
  [HasCountableProducts A3] [HasLimitsOfShape ℕᵒᵖ A3]
  [HasDerivedCategory.{w3} A3] in
/-- The given square localized termwise on strict towers, with the canonical composition
and localization isomorphisms. Source: Stacks 05RU, exact-functor localization
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
def towerSquare (e : F ⋙ G ≅ H ⋙ K) :
    towerDerived F ⋙ towerDerived G ≅ towerDerived H ⋙ towerDerived K :=
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A0 A1).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A0 A1).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A1 A3).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A1 A3).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A0 A2).obj H) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A0 A2).obj H) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A2 A3).obj K) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A2 A3).obj K) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  Functor.mapDerivedCategorySquareIso ((Functor.whiskeringRight ℕᵒᵖ A0 A3).mapIso e)

variable (L0 : DerivedCategory.{w0} (ℕᵒᵖ ⥤ A0) ⥤ DerivedCategory.{w0} A0)
  (eta0 : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ L0)
variable (L1 : DerivedCategory.{w1} (ℕᵒᵖ ⥤ A1) ⥤ DerivedCategory.{w1} A1)
  (eta1 : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ L1)
variable (L2 : DerivedCategory.{w2} (ℕᵒᵖ ⥤ A2) ⥤ DerivedCategory.{w2} A2)
  (eta2 : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ L2)
variable (L3 : DerivedCategory.{w3} (ℕᵒᵖ ⥤ A3) ⥤ DerivedCategory.{w3} A3)
  (eta3 : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ L3)

/-- The four shared Roos models and their four comparisons.
Source: the normalized square construction
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
def SquareData :=
  Σ a0 : Corner L0 eta0, Σ a1 : Corner L1 eta1,
    Σ a2 : Corner L2 eta2, Σ a3 : Corner L3 eta3,
      Comparison a0 a1 F × Comparison a1 a3 G ×
        Comparison a0 a2 H × Comparison a2 a3 K

/-- The `corner0` component of the fixed comparison data.
Source: the normalized square construction
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
abbrev SquareData.corner0 (d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3) :=
  d.1

/-- The `corner3` component of the fixed comparison data.
Source: the normalized square construction
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
abbrev SquareData.corner3 (d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3) :=
  d.2.2.2.1

/-- The `comparisonF` component of the fixed comparison data.
Source: the normalized square construction
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
abbrev SquareData.comparisonF (d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3) :=
  d.2.2.2.2.1

/-- The `comparisonG` component of the fixed comparison data.
Source: the normalized square construction
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
abbrev SquareData.comparisonG (d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3) :=
  d.2.2.2.2.2.1

/-- The `comparisonH` component of the fixed comparison data.
Source: the normalized square construction
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
abbrev SquareData.comparisonH (d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3) :=
  d.2.2.2.2.2.2.1

/-- The `comparisonK` component of the fixed comparison data.
Source: the normalized square construction
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
abbrev SquareData.comparisonK (d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3) :=
  d.2.2.2.2.2.2.2

/-- All equations attached to one fixed square of comparisons.
Source: the square and augmentation calculation
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
def SquareLaws (d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3)
    (e : F ⋙ G ≅ H ⋙ K) : Prop :=
  (∀ N : ℕ → A0,
  G.map (piComparison F N) ≫ piComparison G (fun n ↦ F.obj (N n)) ≫
      Limits.Pi.map (fun n ↦ e.hom.app (N n)) =
    e.hom.app (∏ᶜ N) ≫ K.map (piComparison H N) ≫
      piComparison K (fun n ↦ H.obj (N n))) ∧
  (∀ (N : ℕ → A0) (n : ℕ),
  (G.map (piComparison F N) ≫ piComparison G (fun k ↦ F.obj (N k)) ≫
    Limits.Pi.map (fun k ↦ e.hom.app (N k))) ≫
      Pi.π (fun k ↦ K.obj (H.obj (N k))) n =
    G.map (F.map (Pi.π N n)) ≫ e.hom.app (N n)) ∧
  (∀ (N : ℕ → A0) (n : ℕ),
  G.map (F.map (Pi.π N n)) ≫ e.hom.app (N n) =
    e.hom.app (∏ᶜ N) ≫ K.map (H.map (Pi.π N n))) ∧
  (∀ X : CochainComplex (ℕᵒᵖ ⥤ A0) ℤ,
  (G.mapHomologicalComplex (.up ℤ)).map (d.comparisonF.kappa.hom.app X) ≫
      d.comparisonG.kappa.hom.app ((towerComplex F).obj X) ≫
      roosF.map ((towerMap F G H K e.hom).app X) =
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app (roosF.obj X) ≫
      (K.mapHomologicalComplex (.up ℤ)).map (d.comparisonH.kappa.hom.app X) ≫
      d.comparisonK.kappa.hom.app ((towerComplex H).obj X)) ∧
  (∀ M : DerivedCategory.{w0} (ℕᵒᵖ ⥤ A0),
  G.mapDerivedCategory.map (d.comparisonF.derivedKappa.hom.app M) ≫
      d.comparisonG.derivedKappa.hom.app ((towerDerived F).obj M) ≫
      d.corner3.roos.map ((towerSquare F G H K e).hom.app M) =
    (Functor.mapDerivedCategorySquareIso e).hom.app (d.corner0.roos.obj M) ≫
      K.mapDerivedCategory.map (d.comparisonH.derivedKappa.hom.app M) ≫
      d.comparisonK.derivedKappa.hom.app ((towerDerived H).obj M)) ∧
  (∀ M : DerivedCategory.{w0} (ℕᵒᵖ ⥤ A0),
  G.mapDerivedCategory.map (d.comparisonF.lambda.hom.app M) ≫
      d.comparisonG.lambda.hom.app ((towerDerived F).obj M) ≫
      L3.map ((towerSquare F G H K e).hom.app M) =
    (Functor.mapDerivedCategorySquareIso e).hom.app (L0.obj M) ≫
      K.mapDerivedCategory.map (d.comparisonH.lambda.hom.app M) ≫
      d.comparisonK.lambda.hom.app ((towerDerived H).obj M)) ∧
  (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A0) ℤ)
  (P : CochainComplex A0 ℤ) (gamma : (Functor.const ℕᵒᵖ).obj P ⟶ X.asFunctor),
  G.mapDerivedCategory.map (F.mapDerivedCategory.map (augmentation ⟨P, gamma⟩ (eta0.app X))) ≫
    G.mapDerivedCategory.map (d.comparisonF.lambda.hom.app (DerivedCategory.Q.obj X)) ≫
    d.comparisonG.lambda.hom.app ((towerDerived F).obj (DerivedCategory.Q.obj X)) ≫
    L3.map ((towerDerived G).map ((towerFactors F).hom.app X)) ≫
    L3.map ((towerFactors G).hom.app ((towerComplex F).obj X)) =
  G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
    augmentation ((G.mapHomologicalComplex (.up ℤ)).mapCone
        ((F.mapHomologicalComplex (.up ℤ)).mapCone ⟨P, gamma⟩)) (eta3.app ((towerComplex G).obj
          ((towerComplex F).obj X)))) ∧
  (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A0) ℤ)
  (P : CochainComplex A0 ℤ) (gamma : (Functor.const ℕᵒᵖ).obj P ⟶ X.asFunctor),
  K.mapDerivedCategory.map (H.mapDerivedCategory.map (augmentation ⟨P, gamma⟩ (eta0.app X))) ≫
    K.mapDerivedCategory.map (d.comparisonH.lambda.hom.app (DerivedCategory.Q.obj X)) ≫
    d.comparisonK.lambda.hom.app ((towerDerived H).obj (DerivedCategory.Q.obj X)) ≫
    L3.map ((towerDerived K).map ((towerFactors H).hom.app X)) ≫
    L3.map ((towerFactors K).hom.app ((towerComplex H).obj X)) =
  K.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app P) ≫
    K.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P) ≫
    augmentation ((K.mapHomologicalComplex (.up ℤ)).mapCone
        ((H.mapHomologicalComplex (.up ℤ)).mapCone ⟨P, gamma⟩)) (eta3.app ((towerComplex K).obj
          ((towerComplex H).obj X)))) ∧
  (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A0) ℤ)
  (P : CochainComplex A0 ℤ) (gamma : (Functor.const ℕᵒᵖ).obj P ⟶ X.asFunctor),
  augmentation ((G.mapHomologicalComplex (.up ℤ)).mapCone
        ((F.mapHomologicalComplex (.up ℤ)).mapCone ⟨P, gamma⟩)) (eta3.app ((towerComplex G).obj
          ((towerComplex F).obj X))) ≫
    L3.map (DerivedCategory.Q.map ((towerMap F G H K e.hom).app X)) =
  DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) ≫
    augmentation ((K.mapHomologicalComplex (.up ℤ)).mapCone
        ((H.mapHomologicalComplex (.up ℤ)).mapCone ⟨P, gamma⟩)) (eta3.app ((towerComplex K).obj
          ((towerComplex H).obj X))))

/-- All clauses of square coherence, with the very same corners and comparisons.
Fields are conclusions, and specify actual chain maps and natural isomorphisms.
Source: the final blueprint comparison paragraph and the DAG's projection calculation
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
def Coherence (e : F ⋙ G ≅ H ⋙ K) :=
  ∃ d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3,
    SquareLaws F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3 d e

omit [HasCountableProducts A0] [HasCountableProducts A1]
  [HasCountableProducts A2] [HasCountableProducts A3]
  [HasLimitsOfShape ℕᵒᵖ A0] [HasLimitsOfShape ℕᵒᵖ A1]
  [HasLimitsOfShape ℕᵒᵖ A2] [HasLimitsOfShape ℕᵒᵖ A3]
  [HasDerivedCategory.{w0} (ℕᵒᵖ ⥤ A0)] [HasDerivedCategory.{w1} (ℕᵒᵖ ⥤ A1)]
  [HasDerivedCategory.{w2} (ℕᵒᵖ ⥤ A2)] [HasDerivedCategory.{w3} (ℕᵒᵖ ⥤ A3)] in
private theorem square_factors (e : F ⋙ G ≅ H ⋙ K) (P : CochainComplex A0 ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
        K.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app P) ≫
        K.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F G).inv.app
    (DerivedCategory.Q.obj P))).1
  simp only [Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]

private theorem tower_square_factors (e : F ⋙ G ≅ H ⋙ K)
    (X : CochainComplex (ℕᵒᵖ ⥤ A0) ℤ) :
    (towerSquare F G H K e).hom.app (DerivedCategory.Q.obj X) ≫
        (towerDerived K).map ((towerFactors H).hom.app X) ≫
        (towerFactors K).hom.app ((towerComplex H).obj X) =
      (towerDerived G).map ((towerFactors F).hom.app X) ≫
        (towerFactors G).hom.app ((towerComplex F).obj X) ≫
        DerivedCategory.Q.map ((towerMap F G H K e.hom).app X) := by
  let : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A0 A1).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A0 A1).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A1 A3).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A1 A3).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A0 A2).obj H) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A0 A2).obj H) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A2 A3).obj K) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A2 A3).obj K) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  delta towerMap
  exact square_factors
    ((Functor.whiskeringRight ℕᵒᵖ A0 A1).obj F)
    ((Functor.whiskeringRight ℕᵒᵖ A1 A3).obj G)
    ((Functor.whiskeringRight ℕᵒᵖ A0 A2).obj H)
    ((Functor.whiskeringRight ℕᵒᵖ A2 A3).obj K)
    ((Functor.whiskeringRight ℕᵒᵖ A0 A3).mapIso e) X

private theorem derived_square
    (a0 : Corner L0 eta0) (a1 : Corner L1 eta1)
    (a2 : Corner L2 eta2) (a3 : Corner L3 eta3)
    (cF : Comparison a0 a1 F) (cG : Comparison a1 a3 G)
    (cH : Comparison a0 a2 H) (cK : Comparison a2 a3 K)
    (e : F ⋙ G ≅ H ⋙ K)
    (hc : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A0) ℤ,
      (G.mapHomologicalComplex (.up ℤ)).map (cF.kappa.hom.app X) ≫
        cG.kappa.hom.app ((towerComplex F).obj X) ≫
        roosF.map ((towerMap F G H K e.hom).app X) =
      (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app (roosF.obj X) ≫
        (K.mapHomologicalComplex (.up ℤ)).map (cH.kappa.hom.app X) ≫
        cK.kappa.hom.app ((towerComplex H).obj X))
    (M : DerivedCategory.{w0} (ℕᵒᵖ ⥤ A0)) :
    G.mapDerivedCategory.map (cF.derivedKappa.hom.app M) ≫
        cG.derivedKappa.hom.app ((towerDerived F).obj M) ≫
        a3.roos.map ((towerSquare F G H K e).hom.app M) =
      (Functor.mapDerivedCategorySquareIso e).hom.app (a0.roos.obj M) ≫
        K.mapDerivedCategory.map (cH.derivedKappa.hom.app M) ≫
        cK.derivedKappa.hom.app ((towerDerived H).obj M) := by
  let α : a0.roos ⋙ F.mapDerivedCategory ⋙ G.mapDerivedCategory ⟶
      (towerDerived H ⋙ towerDerived K) ⋙ a3.roos :=
    Functor.whiskerRight cF.derivedKappa.hom G.mapDerivedCategory ≫
      Functor.whiskerLeft (towerDerived F) cG.derivedKappa.hom ≫
      Functor.whiskerRight (towerSquare F G H K e).hom a3.roos
  let β : a0.roos ⋙ F.mapDerivedCategory ⋙ G.mapDerivedCategory ⟶
      (towerDerived H ⋙ towerDerived K) ⋙ a3.roos :=
    Functor.whiskerLeft a0.roos (Functor.mapDerivedCategorySquareIso e).hom ≫
      Functor.whiskerRight cH.derivedKappa.hom K.mapDerivedCategory ≫
      Functor.whiskerLeft (towerDerived H) cK.derivedKappa.hom
  have h : α = β := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A0) (.up ℤ))
    intro X
    change G.mapDerivedCategory.map (cF.derivedKappa.hom.app (DerivedCategory.Q.obj X)) ≫
        cG.derivedKappa.hom.app ((towerDerived F).obj (DerivedCategory.Q.obj X)) ≫
        a3.roos.map ((towerSquare F G H K e).hom.app (DerivedCategory.Q.obj X)) =
      (Functor.mapDerivedCategorySquareIso e).hom.app
        (a0.roos.obj (DerivedCategory.Q.obj X)) ≫
        K.mapDerivedCategory.map (cH.derivedKappa.hom.app (DerivedCategory.Q.obj X)) ≫
        cK.derivedKappa.hom.app ((towerDerived H).obj (DerivedCategory.Q.obj X))
    apply (cancel_mono (a3.roos.map
      ((towerDerived K).map ((towerFactors H).hom.app X) ≫
        (towerFactors K).hom.app ((towerComplex H).obj X)) ≫
      a3.factors.hom.app ((towerComplex K).obj ((towerComplex H).obj X)))).1
    simp only [Category.assoc]
    rw [← a3.roos.map_comp_assoc]
    rw [tower_square_factors]
    rw [a3.roos.map_comp]
    simp only [Category.assoc]
    simp only [Functor.map_comp, Category.assoc]
    have hn := a3.factors.hom.naturality
      ((towerMap F G H K e.hom).app X)
    dsimp only [Functor.comp_map] at hn
    erw [hn]
    have hFG := path_descent a0 a1 a3 F G cF cG X
    have hHK := path_descent a0 a2 a3 H K cH cK X
    simp only [Functor.map_comp, Category.assoc] at hFG hHK
    erw [reassoc_of% hFG, hHK]
    have he := (Functor.mapDerivedCategorySquareIso e).hom.naturality
      (a0.factors.hom.app X)
    dsimp only [Functor.comp_map] at he
    erw [← reassoc_of% he]
    erw [reassoc_of% square_factors F G H K e (roosF.obj X)]
    erw [← DerivedCategory.Q.map_comp_assoc, ← DerivedCategory.Q.map_comp]
    simp only [Category.assoc]
    erw [hc X]
    erw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp]
  exact congr_app h M

private theorem normalized_square
    (a0 : Corner L0 eta0) (a1 : Corner L1 eta1)
    (a2 : Corner L2 eta2) (a3 : Corner L3 eta3)
    (cF : Comparison a0 a1 F) (cG : Comparison a1 a3 G)
    (cH : Comparison a0 a2 H) (cK : Comparison a2 a3 K)
    (e : F ⋙ G ≅ H ⋙ K)
    (hr : ∀ M : DerivedCategory.{w0} (ℕᵒᵖ ⥤ A0),
      G.mapDerivedCategory.map (cF.derivedKappa.hom.app M) ≫
        cG.derivedKappa.hom.app ((towerDerived F).obj M) ≫
        a3.roos.map ((towerSquare F G H K e).hom.app M) =
      (Functor.mapDerivedCategorySquareIso e).hom.app (a0.roos.obj M) ≫
        K.mapDerivedCategory.map (cH.derivedKappa.hom.app M) ≫
        cK.derivedKappa.hom.app ((towerDerived H).obj M))
    (M : DerivedCategory.{w0} (ℕᵒᵖ ⥤ A0)) :
    G.mapDerivedCategory.map (cF.lambda.hom.app M) ≫
        cG.lambda.hom.app ((towerDerived F).obj M) ≫
        L3.map ((towerSquare F G H K e).hom.app M) =
      (Functor.mapDerivedCategorySquareIso e).hom.app (L0.obj M) ≫
        K.mapDerivedCategory.map (cH.lambda.hom.app M) ≫
        cK.lambda.hom.app ((towerDerived H).obj M) := by
  simp only [cF.conjugation, cG.conjugation, cH.conjugation, cK.conjugation,
    Functor.map_comp, Category.assoc]
  rw [← G.mapDerivedCategory.map_comp_assoc
    (a1.theta.inv.app ((towerDerived F).obj M))
    (a1.theta.hom.app ((towerDerived F).obj M)), Iso.inv_hom_id_app,
    G.mapDerivedCategory.map_id, Category.id_comp]
  rw [← K.mapDerivedCategory.map_comp_assoc
    (a2.theta.inv.app ((towerDerived H).obj M))
    (a2.theta.hom.app ((towerDerived H).obj M)), Iso.inv_hom_id_app,
    K.mapDerivedCategory.map_id, Category.id_comp]
  rw [← a3.theta.inv.naturality]
  erw [reassoc_of% hr M]
  erw [(Functor.mapDerivedCategorySquareIso e).hom.naturality_assoc]
  rfl

private theorem augmentation_square (e : F ⋙ G ≅ H ⋙ K)
    (X : CochainComplex (ℕᵒᵖ ⥤ A0) ℤ) (P : CochainComplex A0 ℤ)
    (gamma : (Functor.const ℕᵒᵖ).obj P ⟶ X.asFunctor) :
    DerivedCategory.Q.map (limit.lift _
        ((G.mapHomologicalComplex (.up ℤ)).mapCone
          ((F.mapHomologicalComplex (.up ℤ)).mapCone ⟨P, gamma⟩))) ≫
      eta3.app ((towerComplex G).obj ((towerComplex F).obj X)) ≫
      L3.map (DerivedCategory.Q.map ((towerMap F G H K e.hom).app X)) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) ≫
      DerivedCategory.Q.map (limit.lift _
        ((K.mapHomologicalComplex (.up ℤ)).mapCone
          ((H.mapHomologicalComplex (.up ℤ)).mapCone ⟨P, gamma⟩))) ≫
      eta3.app ((towerComplex K).obj ((towerComplex H).obj X)) := by
  let t := (towerMap F G H K e.hom).app X
  erw [← eta3.naturality t]
  dsimp only [Functor.comp_map]
  simp only [← DerivedCategory.Q.map_comp_assoc]
  congr 1
  apply congrArg DerivedCategory.Q.map
  apply limit.hom_ext
  intro n
  simp only [Category.assoc, roosLimitFunctor, Functor.comp_map, lim_map, limMap_π,
    HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj]
  erw [limit.lift_π_assoc, limit.lift_π]
  apply HomologicalComplex.Hom.ext
  funext q
  dsimp only [t]
  delta towerMap
  exact e.hom.naturality ((gamma.app n).f q)

end Square
private theorem cornerData
    {C : Type c0} [Category.{d0} C] [EssentiallySmall.{r0} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{r0}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r0}] (R : Sheaf J RingCat.{r0})
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{r0} R)]
    [HasDerivedCategory.{w0} (ringedSiteModules.{r0} R)]
    [HasDerivedCategory.{w0} (ℕᵒᵖ ⥤ ringedSiteModules.{r0} R)]
    (L : DerivedCategory.{w0} (ℕᵒᵖ ⥤ ringedSiteModules.{r0} R) ⥤
      DerivedCategory.{w0} (ringedSiteModules.{r0} R))
    (eta : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ L)
    (hL : L.IsRightDerivedFunctor eta
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{r0} R) (.up ℤ))) :
    ∃ a : Corner L eta, ∀ X,
      eta.app X ≫ a.theta.hom.app (DerivedCategory.Q.obj X) ≫ a.factors.hom.app X =
        DerivedCategory.Q.map (roosι X) := by
  classical
  let A := ringedSiteModules.{r0} R
  let : IsGrothendieckAbelian.{r0} A := moduleSheaves_grothendieck J R
  let : IsGrothendieckAbelian.{r0} (ℕᵒᵖ ⥤ A) := tower_grothendieck A
  let W := HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)
  have hinv : W.IsInvertedBy (roosF ⋙ DerivedCategory.Q.{w0}) := by
    intro X Y f hf
    have : QuasiIso f := hf
    have : QuasiIso (roosF.map f) := roos_map_quasiIso f
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map (roosF.map f)))
  let CF := Localization.lift (roosF ⋙ DerivedCategory.Q.{w0}) hinv DerivedCategory.Q
  let k := (Localization.fac (roosF ⋙ DerivedCategory.Q.{w0}) hinv DerivedCategory.Q).symm
  have hCF : CF.IsRightDerivedFunctor (roosDerivedUnit k) W := by
    exact roos_universal W DerivedCategory.Q _ _ CF k
      (Functor.whiskerRight roosInclusion DerivedCategory.Q)
      (CochainComplex.kInjectiveResolutionFunctor.{r0} (ℕᵒᵖ ⥤ A))
      (CochainComplex.toKInjectiveResolution.{r0} (ℕᵒᵖ ⥤ A))
      (fun X ↦ (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ X).2)
      (fun X ↦ by
        have := roos_inclusion_quasiIso
          ((CochainComplex.kInjectiveResolutionFunctor.{r0} (ℕᵒᵖ ⥤ A)).obj X)
        exact inferInstanceAs (IsIso (DerivedCategory.Q.map (roosι _))))
  let := hCF
  let := hL
  let rho := CF.rightDerivedUnique L (roosDerivedUnit k) eta W
  have hunit (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      DerivedCategory.Q.map (roosι X) ≫ k.hom.app X ≫
        rho.hom.app (DerivedCategory.Q.obj X) = eta.app X := by
    have h := CF.rightDerivedNatTrans_app L (roosDerivedUnit k) eta W (𝟙 _) X
    simpa [rho, Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      roosDerivedUnit, roosInclusion, roosLimitFunctor,
      Functor.rightDerivedNatTrans, Category.assoc] using h
  have hn (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      eta.app X ≫ rho.inv.app (DerivedCategory.Q.obj X) ≫ k.inv.app X =
        DerivedCategory.Q.map (roosι X) := by
    rw [← hunit]
    simp
  exact ⟨⟨CF, k.symm, rho.symm, fun I _ _ ↦ hn I⟩, hn⟩

end CategoryTheory.NormalizedLimitSquare
