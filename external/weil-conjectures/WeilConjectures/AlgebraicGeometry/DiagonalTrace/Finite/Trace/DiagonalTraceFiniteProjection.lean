/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEvaluation
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
import all WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Projection coherence of the normalized finite direct-image square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u a b v z w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory

private theorem evaluation_normalization
    {A B : Type (a + 1)} [Category.{a} A] [Category.{a} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive]
    (Rt : DiagonalRightDerived ((Functor.whiskeringRight ℕᵒᵖ A B).obj F))
    (Rf : DiagonalRightDerived F) (n : ℕ)
    (s : ExactSquare ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) F
      ((evaluation ℕᵒᵖ A).obj (op n)) ((evaluation ℕᵒᵖ B).obj (op n))
      Rt Rf (Iso.refl _)) (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map (Rt.η.app P) ≫
        s.iso.hom.app (DerivedCategory.Q.obj P) ≫
        Rf.R.map (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app P) =
      ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategoryFactors.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        Rf.η.app ((((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).obj P) := by
  have h := s.normalization P
  simp only [Iso.refl_hom, NatTrans.mapHomologicalComplex_id, NatTrans.id_app] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

private theorem normalized_projection
    {A : Type a} [Category.{v} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    {B : Type b} [Category.{z} B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    (F : A ⥤ B) [F.Additive]
    (LX : DiagonalRlim A) (LY : DiagonalRlim B)
    (Rf : DiagonalRightDerived F)
    (Rt : DiagonalRightDerived ((Functor.whiskeringRight ℕᵒᵖ A B).obj F))
    (c₀ : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ F ≅
      (Functor.whiskeringRight ℕᵒᵖ A B).obj F ⋙ lim)
    (c : LX.R ⋙ Rf.R ≅ Rt.R ⋙ LY.R)
    (hc : ∀ P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      Rf.η.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj P) ≫
          Rf.R.map (LX.η.app P) ≫ c.hom.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex c₀.hom (.up ℤ)).app P) ≫
          LY.η.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
            (.up ℤ)).obj P) ≫ LY.R.map (Rt.η.app P))
    (n : ℕ)
    (e : Rt.R ⋙ ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory ≅
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ⋙ Rf.R)
    (he : ∀ P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map (Rt.η.app P) ≫
          e.hom.app (DerivedCategory.Q.obj P) ≫
          Rf.R.map (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app P) =
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategoryFactors.hom.app
            ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
              (.up ℤ)).obj P) ≫
          Rf.η.app ((((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).obj P))
    (hπ : ∀ H : ℕᵒᵖ ⥤ A,
      c₀.hom.app H ≫ limit.π (H ⋙ F) (op n) = F.map (limit.π H (op n)))
    (M : DerivedCategory (ℕᵒᵖ ⥤ A)) :
    c.hom.app M ≫ (LY.projection n).app (Rt.R.obj M) ≫ e.hom.app M =
      Rf.R.map ((LX.projection n).app M) := by
  let FT := (Functor.whiskeringRight ℕᵒᵖ A B).obj F
  let FTc := FT.mapHomologicalComplex (.up ℤ)
  have := towerComparison_limPreservesKInjective (A := A)
  obtain ⟨α, hα, hαapp⟩ := towerComparison_existsComposite
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A) F LX.R Rf.R LX.η Rf.η LX.computation
    (fun I hI ↦ by
      have := hI
      exact Rf.computation _ inferInstance)
  have := hα
  let γ₁ : LX.R ⋙ Rf.R ⟶ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ⋙ Rf.R :=
    c.hom ≫ Functor.whiskerLeft Rt.R (LY.projection n) ≫ e.hom
  let γ₂ : LX.R ⋙ Rf.R ⟶ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ⋙ Rf.R :=
    Functor.whiskerRight (LX.projection n) Rf.R
  have hγ : γ₁ = γ₂ := by
    apply Functor.rightDerived_ext (LX.R ⋙ Rf.R) α
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
    apply NatTrans.ext
    funext X
    let limπ := (NatTrans.mapHomologicalComplex
      (lim.π (op n) : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⟶
        (evaluation ℕᵒᵖ A).obj (op n)) (.up ℤ)).app X
    let limπ' := (NatTrans.mapHomologicalComplex
      (lim.π (op n) : (lim : (ℕᵒᵖ ⥤ B) ⥤ B) ⟶
        (evaluation ℕᵒᵖ B).obj (op n)) (.up ℤ)).app (FTc.obj X)
    let cX := (NatTrans.mapHomologicalComplex c₀.hom (.up ℤ)).app X
    have hchain : cX ≫ limπ' = (F.mapHomologicalComplex (.up ℤ)).map limπ := by
      apply HomologicalComplex.hom_ext
      intro i
      exact hπ (X.X i)
    have hF := diagonalMapComposite DerivedCategory.Q cX limπ'
      ((F.mapHomologicalComplex (.up ℤ)).map limπ)
      (Rf.η.app ((((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).obj X))
      (Rf.η.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X) ≫
        Rf.R.map (DerivedCategory.Q.map limπ)) hchain (Rf.η.naturality limπ)
    have hX := congrArg Rf.R.map (LX.normalization X n)
    simp only [CategoryTheory.Functor.map_comp] at hX
    have hmain :
        (Rf.η.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X) ≫
          Rf.R.map (LX.η.app X)) ≫ γ₁.app (DerivedCategory.Q.obj X) =
        (Rf.η.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X) ≫
          Rf.R.map (LX.η.app X)) ≫ γ₂.app (DerivedCategory.Q.obj X) := by
      apply (cancel_mono (Rf.R.map
        (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app X))).mp
      simpa only [γ₁, γ₂, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Category.assoc] using diagonalProjectionDiagram
        (Rf.η.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X))
        (Rf.R.map (LX.η.app X)) (c.hom.app (DerivedCategory.Q.obj X))
        (DerivedCategory.Q.map cX) (LY.η.app (FTc.obj X)) (LY.R.map (Rt.η.app X))
        ((LY.projection n).app (Rt.R.obj (DerivedCategory.Q.obj X)))
        ((LY.projection n).app (DerivedCategory.Q.obj (FTc.obj X)))
        (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map (Rt.η.app X))
        (e.hom.app (DerivedCategory.Q.obj X))
        (Rf.R.map (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app X))
        (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategoryFactors.hom.app (FTc.obj X))
        (Rf.η.app ((((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).obj X))
        (DerivedCategory.Q.map limπ') (Rf.R.map (DerivedCategory.Q.map limπ))
        (Rf.R.map ((LX.projection n).app (DerivedCategory.Q.obj X)))
        (hc X) ((LY.projection n).naturality (Rt.η.app X))
        (he X) (LY.normalization (FTc.obj X) n) hF hX
    exact (congrArg (fun z ↦ z ≫ γ₁.app (DerivedCategory.Q.obj X)) (hαapp X)).trans
      (hmain.trans
        (congrArg (fun z ↦ z ≫ γ₂.app (DerivedCategory.Q.obj X)) (hαapp X)).symm)
  exact NatTrans.congr_app hγ M

/-- The normalized limit/direct-image comparison commutes with the actual
unit-normalized evaluation/direct-image comparison.

Source: diagonal tower limit proof (1), projection compatibility of derived
right adjoints; Stacks Tag 0A07.
(blueprint: lem-sfb-diagonal-trace-finite-evaluation-projection).

Proof: both sides are natural transformations out of the right derived functor
of limit followed by ordinary direct image. The exact constant-tower left
adjoint makes limit preserve K-injectives, so this composite computes that
right derived functor. Its universal property reduces the equality to the
common units on complexes. Insert the full normalization of the limit square
and of the evaluation square. Naturality of the limit projection moves the
tower direct-image unit to evaluation. The remaining equality is limit.post
followed by the ordinary projection, which is direct image of the projection.
Thus no levelwise faithfulness of arbitrary derived morphisms is used. -/
theorem diagonalTrace_finiteEvaluation_projection
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l (ULift.{u} (Padic l)) f)
    (M : DerivedCategory (DiagonalSystems l X)) (n : ℕ) :
    p.limits.iso.hom.app M ≫ (p.LS.projection n).app (p.Rt.R.obj M) ≫
        (finiteEvaluationSquare l f p.Rt p.Rf n).iso.hom.app M =
      p.Rf.R.map ((p.LX.projection n).app M) := by
  have : IsGrothendieckAbelian.{u + 1} (DiagonalMod l X) :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) X
  have : IsGrothendieckAbelian.{u + 1} (DiagonalSystems l X) :=
    CategoryTheory.RingedStrictTowerProof.tower_grothendieck (DiagonalMod l X)
  apply normalized_projection
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
    p.LX p.LS p.Rf p.Rt p.limits.ordinary p.limits.iso p.limits.normalization n
    (finiteEvaluationSquare l f p.Rt p.Rf n).iso ?_ ?_ M
  · exact evaluation_normalization
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
      p.Rt p.Rf n (finiteEvaluationSquare l f p.Rt p.Rf n)
  · intro H
    rw [p.limits.ordinary_eq]
    exact limit.post_π H _ (op n)

end AlgebraicGeometry.ProEtale.DiagonalTrace
