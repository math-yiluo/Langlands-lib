/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionData

import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientOrdinaryComparison
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # The finite quotient transition square

This is the strict finite evaluation compatibility used to transport completed
pullback presentations. Its proof uses the prescribed ordinary quotient square
and descends the model computation through K-flat resolutions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedReductionModuleTowerFunctor completedTowerModulePullback
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

private theorem completedReductionCompositeCounitNat_app
    {B C D E B' C' D' E' : Type*}
    [Category* B] [Category* C] [Category* D] [Category* E]
    [Category* B'] [Category* C'] [Category* D'] [Category* E']
    (QB : B ⥤ B') (QC : C ⥤ C') (QD : D ⥤ D') (QE : E ⥤ E')
    (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E)
    (LF : B' ⥤ C') (LG : C' ⥤ D') (LH : D' ⥤ E')
    (α : QB ⋙ LF ⟶ F ⋙ QC) (β : QC ⋙ LG ⟶ G ⋙ QD)
    (γ : QD ⋙ LH ≅ H ⋙ QE)
    (P : B) :
    (completedReductionCompositeCounitNat QB QC QD QE F G H LF LG LH α β γ).app P =
      LH.map (LG.map (α.app P) ≫ β.app (F.obj P)) ≫ γ.hom.app ((F ⋙ G).obj P) := by
  unfold completedReductionCompositeCounitNat
  rfl

private theorem completedReductionFiniteModelNat_app (n : ℕ)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :
    (completedReductionFiniteModelNat g d n).app P =
      completedReductionFiniteModelMap g d n P := by
  dsimp only [completedReductionFiniteModelNat, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    completedReductionComplexCounitNat]
  unfold completedReductionFiniteModelMap pbcComplexCounit
    Functor.leftDerivedCounitOnComplex
  rfl

private theorem completedReductionPulledModelNat_app (n : ℕ)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :
    (completedReductionPulledModelNat g d n).app P =
      completedReductionPulledModelMap g d n P := by
  unfold completedReductionPulledModelNat completedReductionPulledModelMap
  rfl

private def restrictedTransition
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {B : C ⥤ D} {Fb : C ⥤ E} {Fa : C ⥤ F}
    {Rb : E ⥤ D} {Rq : F ⥤ E} {Ra : F ⥤ D}
    (eb : B ⟶ Fb ⋙ Rb) (τ : Fb ⟶ Fa ⋙ Rq) (e : Rq ⋙ Rb ≅ Ra) :
    B ⟶ Fa ⋙ Ra :=
  eb ≫ Functor.whiskerRight τ Rb ≫ (Functor.associator Fa Rq Rb).hom ≫
    Functor.whiskerLeft Fa e.hom

private theorem restrictedTransition_app
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {B : C ⥤ D} {Fb : C ⥤ E} {Fa : C ⥤ F}
    {Rb : E ⥤ D} {Rq : F ⥤ E} {Ra : F ⥤ D}
    (eb : B ⟶ Fb ⋙ Rb) (τ : Fb ⟶ Fa ⋙ Rq) (e : Rq ⋙ Rb ≅ Ra) (K : C) :
    (restrictedTransition eb τ e).app K =
      eb.app K ≫ Rb.map (τ.app K) ≫ e.hom.app (Fa.obj K) := by
  simp only [restrictedTransition, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp]

attribute [local irreducible] restrictedTransition

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarCounit_isIso
    {T : Scheme.{u}} {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (P : CochainComplex (pbcModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    IsIso (pbcComplexCounit φ P) := by
  have := pbcExtensionCounit_isIso φ P hP
  dsimp only [pbcComplexCounit]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteModel_isIso (n : ℕ)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := pbcAdicCompletion Y d) P) :
    IsIso (completedReductionFiniteModelMap g d n P) := by
  have := scalarCounit_isIso (completedReductionProjection Y d n) P hP
  dsimp only [completedReductionFiniteModelMap]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exactFunctorComp_factors
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj P) ≫
      H.mapDerivedCategoryFactors.hom.app P =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) := by
  dsimp only [Iso.trans_hom, NatTrans.comp_app]
  erw [Category.assoc, Functor.mapDerivedCategoryNatIso_fac,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factors]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedRestrictionComp_factors
    {T : Scheme.{u}} {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (P : CochainComplex (pbcModules T B) ℤ) :
    (pbcDerivedRestrictComp φ ψ χ h).hom.app (DerivedCategory.Q.obj P) ≫
      (pbcRestrict χ).mapDerivedCategoryFactors.hom.app P =
    (pbcDerivedRestrict φ).map ((pbcRestrict ψ).mapDerivedCategoryFactors.hom.app P) ≫
      (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
        (((pbcRestrict ψ).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (pbcRestrictComp φ ψ χ h).hom (.up ℤ)).app P) := by
  exact Functor.exactDerivedRestrictionComposition_hom_factors
    (pbcRestrict ψ) (pbcRestrict φ) (pbcRestrict χ)
    (pbcRestrictComp φ ψ χ h) P

private theorem restriction_diagram
    {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    (S : C₁ ⥤ C₂) (R : C₂ ⥤ C₃) (T : C₁ ⥤ C₃) (e : S ⋙ R ≅ T)
    {A P : C₁} {B Q U : C₂} {C V W Z : C₃}
    (m₁ : A ⟶ P) (m₂ : B ⟶ Q) (m₃ : C ⟶ V)
    (t₁ : B ⟶ S.obj A) (t₂ : C ⟶ R.obj B)
    (f₁ : S.obj P ⟶ U) (f₂ : R.obj Q ⟶ W)
    (f₃ : R.obj U ⟶ Z) (f₄ : T.obj P ⟶ Z)
    (u₁ : Q ⟶ U) (u₂ : V ⟶ W) (u₃ : W ⟶ Z)
    (h₁ : t₁ ≫ S.map m₁ ≫ f₁ = m₂ ≫ u₁)
    (h₂ : t₂ ≫ R.map m₂ ≫ f₂ = m₃ ≫ u₂)
    (h₃ : R.map u₁ ≫ f₃ = f₂ ≫ u₃)
    (h₄ : e.hom.app P ≫ f₄ = R.map f₁ ≫ f₃) :
    t₂ ≫ R.map t₁ ≫ e.hom.app A ≫ T.map m₁ ≫ f₄ =
      m₃ ≫ u₂ ≫ u₃ := by
  rw [← e.hom.naturality_assoc m₁]
  dsimp only [Functor.comp_map]
  rw [h₄]
  simp only [← R.map_comp_assoc]
  rw [h₁, R.map_comp]
  simp only [Category.assoc]
  rw [h₃]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ u₃) h₂

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem towerTransition_factors
    {T : Scheme.{u}} (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (P : CochainComplex (pbcTowers T R) ℤ) (a b : ℕ) (h : a ≤ b) :
    (pbcTowerTransition T R b a h).app (DerivedCategory.Q.obj P) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T R)).obj
        (op a)).mapDerivedCategoryFactors.hom.app P =
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T R)).obj
        (op b)).mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T R)).map (homOfLE h).op)
        (.up ℤ)).app P) := by
  simp only [pbcTowerTransition, Localization.liftNatTrans_app,
    Functor.whiskerRight_app, Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  rfl

private theorem model_naturality
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (τ : F ⟶ G) {K L : C} (κ : K ⟶ L) {B A : D}
    (mb : F.obj L ⟶ B) (ma : G.obj L ⟶ A) (v : B ⟶ A)
    (h : τ.app L ≫ ma = mb ≫ v) :
    (F.map κ ≫ mb) ≫ v = τ.app K ≫ (G.map κ ≫ ma) := by
  rw [Category.assoc, ← h, ← Category.assoc, τ.naturality, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pulledModel_transition
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (a b : ℕ) (h : a ≤ b) :
    completedReductionPulledModelMap g d b P ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).map
          (homOfLE h).op) (.up ℤ)).app
        (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
          (((completedReductionModuleTowerFunctor Y d).mapHomologicalComplex (.up ℤ)).obj
            P))) =
    (pbcTowerTransition X (pbcAdicCompletion X d) b a h).app
        ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj
          (DerivedCategory.Q.obj P))) ≫ completedReductionPulledModelMap g d a P := by
  let κ := (completedTowerPullback g d).map
    (completedReductionTowerComplexCounit Y d P) ≫
    completedTowerPullbackComplexCounit g d
      ((completedReductionComplexTowerFunctor Y d).obj P)
  have hh := model_naturality (pbcTowerTransition X (pbcAdicCompletion X d) b a h) κ
    (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
      (op b)).mapDerivedCategoryFactors.hom.app
        (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
          (((completedReductionModuleTowerFunctor Y d).mapHomologicalComplex (.up ℤ)).obj P)))
    _ _ (towerTransition_factors (pbcAdicCompletion X d)
      (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
        (((completedReductionModuleTowerFunctor Y d).mapHomologicalComplex (.up ℤ)).obj P))
      a b h)
  simpa only [κ, pbcTowerEvaluation, completedReductionComplexTowerFunctor,
    Functor.comp_obj, completedReductionPulledModelMap,
    completedReductionCompositeCounitNat_app, completedReductionTowerComplexNat,
    completedReductionPullbackComplexNat] using hh

private theorem paste_squares
    {C : Type*} [Category* C] {A B D E F G H : C}
    {m₁ : A ⟶ B} {b₁ : B ⟶ D} {t : D ⟶ E}
    {d : B ⟶ F} {s : A ⟶ G} {m₂ : G ⟶ F} {b₂ : F ⟶ E}
    {r : G ⟶ H} {k : H ⟶ E}
    (h₁ : b₁ ≫ t = d ≫ b₂) (h₂ : m₁ ≫ d = s ≫ m₂)
    (h₃ : m₂ ≫ b₂ = r ≫ k) :
    m₁ ≫ b₁ ≫ t = s ≫ r ≫ k := by
  rw [h₁, ← Category.assoc, h₂, Category.assoc, h₃]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def whiskeredComparison
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (T : C ⥤ D) (L : D ⥤ E) {Vb Va : E ⥤ F} (τ : Vb ⟶ Va)
    {G : C ⥤ F} (e : T ⋙ L ⋙ Va ⟶ G) : T ⋙ L ⋙ Vb ⟶ G :=
  Functor.whiskerLeft T (Functor.whiskerLeft L τ) ≫ e

private theorem whiskeredComparison_app
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (T : C ⥤ D) (L : D ⥤ E) {Vb Va : E ⥤ F} (τ : Vb ⟶ Va)
    {G : C ⥤ F} (e : T ⋙ L ⋙ Va ⟶ G) (K : C) :
    (whiskeredComparison T L τ e).app K = τ.app (L.obj (T.obj K)) ≫ e.app K := by
  rfl

attribute [local irreducible] whiskeredComparison

private theorem mapComplex_square
    {C T U D B₀ B A₀ A E : Type*}
    [Category* C] [Category* T] [Category* U] [Category* D]
    [Category* B₀] [Category* B] [Category* A₀] [Category* A] [Category* E]
    [Preadditive C] [Preadditive T] [Preadditive U] [Preadditive D]
    [Preadditive B₀] [Preadditive B] [Preadditive A₀] [Preadditive A]
    (H : C ⥤ T) (L : T ⥤ U) (Vb Va : U ⥤ D)
    (Eb : C ⥤ B₀) (Fb : B₀ ⥤ B) (Ea : C ⥤ A₀) (Fa : A₀ ⥤ A)
    (Rb : B ⥤ D) (Rq : A ⥤ B) (Ra : A ⥤ D)
    [H.Additive] [L.Additive] [Vb.Additive] [Va.Additive]
    [Eb.Additive] [Fb.Additive] [Ea.Additive] [Fa.Additive]
    [Rb.Additive] [Rq.Additive] [Ra.Additive]
    (eb : H ⋙ L ⋙ Vb ⟶ Eb ⋙ Fb ⋙ Rb) (ea : H ⋙ L ⋙ Va ⟶ Ea ⋙ Fa ⋙ Ra)
    (τ : Eb ⋙ Fb ⟶ Ea ⋙ Fa ⋙ Rq) (κ : Vb ⟶ Va) (e : Rq ⋙ Rb ≅ Ra)
    (hh : ∀ M, eb.app M ≫ Rb.map (τ.app M) ≫ e.hom.app (Fa.obj (Ea.obj M)) =
      κ.app (L.obj (H.obj M)) ≫ ea.app M)
    (Q : CochainComplex D ℤ ⥤ E) (P : CochainComplex C ℤ) :
    Q.map ((NatTrans.mapHomologicalComplex eb (.up ℤ)).app P) ≫
      Q.map ((Rb.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app P)) ≫
      Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        ((Fa.mapHomologicalComplex (.up ℤ)).obj
          ((Ea.mapHomologicalComplex (.up ℤ)).obj P))) =
    Q.map ((NatTrans.mapHomologicalComplex κ (.up ℤ)).app
      ((L.mapHomologicalComplex (.up ℤ)).obj
        ((H.mapHomologicalComplex (.up ℤ)).obj P))) ≫
      Q.map ((NatTrans.mapHomologicalComplex ea (.up ℤ)).app P) := by
  rw [← Q.map_comp_assoc, ← Q.map_comp, ← Q.map_comp]
  apply congrArg Q.map
  ext i : 1
  simpa only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_obj_X,
    Category.assoc] using hh (P.X i)

private theorem normalized_evaluation_square
    {M K A₀ B₀ C₀ A B C : Type*}
    [Category* M] [Category* K] [Category* A₀] [Category* B₀] [Category* C₀]
    [Category* A] [Category* B] [Category* C]
    (Q : M ⥤ K) (Fa : M ⥤ A₀) (Fb : M ⥤ B₀) (Fc Fd : M ⥤ C₀)
    (Qa : A₀ ⥤ A) (Qb : B₀ ⥤ B) (Qc : C₀ ⥤ C)
    (Ha : K ⥤ A) (Hb : K ⥤ B) (Hc Hd : K ⥤ C)
    (Ra : A₀ ⥤ B₀) (Rb : B₀ ⥤ C₀) (Rc : A₀ ⥤ C₀)
    (Sa : A ⥤ B) (Sb : B ⥤ C) (Sc : A ⥤ C)
    (δa : Qa ⋙ Sa ≅ Ra ⋙ Qb) (δb : Qb ⋙ Sb ≅ Rb ⋙ Qc)
    (δc : Qa ⋙ Sc ≅ Rc ⋙ Qc) (e : Sa ⋙ Sb ≅ Sc)
    (γa : ∀ P, Ha.obj (Q.obj P) ⟶ Qa.obj (Fa.obj P))
    (γb : ∀ P, Hb.obj (Q.obj P) ⟶ Qb.obj (Fb.obj P))
    (γc : ∀ P, Hc.obj (Q.obj P) ⟶ Qc.obj (Fc.obj P))
    (γd : ∀ P, Hd.obj (Q.obj P) ⟶ Qc.obj (Fd.obj P))
    (ta : Hb ⟶ Ha ⋙ Sa) (tb : Hc ⟶ Hb ⋙ Sb) (td : Hd ⟶ Ha ⋙ Sc)
    (t : ∀ P, Hc.obj (Q.obj P) ⟶ Hd.obj (Q.obj P))
    (ua : ∀ P, Fb.obj P ⟶ Ra.obj (Fa.obj P))
    (ub : ∀ P, Fc.obj P ⟶ Rb.obj (Fb.obj P))
    (ud : ∀ P, Fc.obj P ⟶ Fd.obj P)
    (vd : ∀ P, Fd.obj P ⟶ Rc.obj (Fa.obj P))
    (k : ∀ P, Qc.obj (Rb.obj (Ra.obj (Fa.obj P))) ⟶ Qc.obj (Rc.obj (Fa.obj P)))
    (S : M → Prop)
    (ha : ∀ P, S P → γb P ≫ Qb.map (ua P) =
      ta.app (Q.obj P) ≫ Sa.map (γa P) ≫ δa.hom.app (Fa.obj P))
    (hb : ∀ P, S P → γc P ≫ Qc.map (ub P) =
      tb.app (Q.obj P) ≫ Sb.map (γb P) ≫ δb.hom.app (Fb.obj P))
    (hc : ∀ P, S P → γd P ≫ Qc.map (vd P) =
      td.app (Q.obj P) ≫ Sc.map (γa P) ≫ δc.hom.app (Fa.obj P))
    (ho : ∀ P, Qc.map (ub P) ≫ Qc.map (Rb.map (ua P)) ≫ k P =
      Qc.map (ud P) ≫ Qc.map (vd P))
    (hp : ∀ P, γc P ≫ Qc.map (ud P) = t P ≫ γd P)
    (he : ∀ P, e.hom.app (Qa.obj (Fa.obj P)) ≫ δc.hom.app (Fa.obj P) =
      Sb.map (δa.hom.app (Fa.obj P)) ≫ δb.hom.app (Ra.obj (Fa.obj P)) ≫ k P)
    (hmono : ∀ P, S P → Mono (Sc.map (γa P) ≫ δc.hom.app (Fa.obj P))) :
    ∀ P, S P → (restrictedTransition tb ta e).app (Q.obj P) =
      t P ≫ td.app (Q.obj P) := by
  intro P hP
  have := hmono P hP
  apply (cancel_mono (Sc.map (γa P) ≫ δc.hom.app (Fa.obj P))).mp
  rw [restrictedTransition_app]
  simp only [Category.assoc]
  have hn := δb.hom.naturality (ua P)
  dsimp only [Functor.comp_map] at hn
  have hd := restriction_diagram Sa Sb Sc e
    (γa P) (γb P) (γc P) (ta.app (Q.obj P)) (tb.app (Q.obj P))
    (δa.hom.app (Fa.obj P)) (δb.hom.app (Fb.obj P))
    (δb.hom.app (Ra.obj (Fa.obj P)) ≫ k P) (δc.hom.app (Fa.obj P))
    (Qb.map (ua P)) (Qc.map (ub P)) (Qc.map (Rb.map (ua P)) ≫ k P)
    (ha P hP).symm (hb P hP).symm
    (by simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ k P) hn)
    (he P)
  exact hd.trans (paste_squares (ho P) (hp P) (hc P hP))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical finite evaluation isomorphisms commute with each quotient arrow.
Source: CBC finite-reduction compatibility, Steps 4 and 7--8
(blueprint: lem-cbc-finite-quotient-transition-compatibility).
Proof: the prescribed ordinary comparisons commute with the quotient maps. On a
K-flat representative, the defining finite evaluation and finite target transition
normalizations identify the two derived composites with this ordinary square.
The counit of the strict tower is natural in its evaluation transition. Compatibility
of exact restriction with composition identifies the two restriction presentations.
The finite computation map is invertible, so cancellation proves the square on
K-flat representatives. Naturality and a K-flat resolution give it on every object. -/
theorem finite_quotient_transition_compatibility
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (a b : ℕ) (h : a ≤ b) :
    (completedReductionFiniteEvaluation g d b).hom.app K ≫
        (pbcDerivedRestrict (completedReductionProjection X d b)).map
          ((completedReductionTargetTransition g d a b h).app K) ≫
        (pbcDerivedRestrictComp (completedReductionProjection X d b)
          (reductionCoefficientMap X d b a h) (completedReductionProjection X d a)
          (completedReductionProjection_comp X d b a h)).hom.app
            ((completedReductionFiniteTarget g d a).obj K) =
      (pbcTowerTransition X (pbcAdicCompletion X d) b a h).app
          ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj K)) ≫
        (completedReductionFiniteEvaluation g d a).hom.app K := by
  let := completedReductionModuleTowerFunctor_additive Y d
  let := completedTowerModulePullback_additive g d
  let πb := completedReductionProjection X d b
  let πa := completedReductionProjection X d a
  let q := reductionCoefficientMap X d b a h
  let e := pbcDerivedRestrictComp πb q πa (completedReductionProjection_comp X d b a h)
  let H := completedReductionModuleTowerFunctor Y d
  let G := completedTowerModulePullback g d
  let V (n : ℕ) :=
    (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n)
  let Ea := reductionChange Y (completedReductionProjection Y d a)
  let Eb := reductionChange Y (completedReductionProjection Y d b)
  let Ga := completedReductionFiniteModules g d a
  let Gb := completedReductionFiniteModules g d b
  let Fa := Ea.mapHomologicalComplex (.up ℤ) ⋙ Ga.mapHomologicalComplex (.up ℤ)
  let Fb := Eb.mapHomologicalComplex (.up ℤ) ⋙ Gb.mapHomologicalComplex (.up ℤ)
  let Fc := H.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ⋙
    (V b).mapHomologicalComplex (.up ℤ)
  let Fd := H.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ⋙
    (V a).mapHomologicalComplex (.up ℤ)
  let Hc := completedReductionTower Y d ⋙ completedTowerPullback g d ⋙
    pbcTowerEvaluation X (pbcAdicCompletion X d) b
  let Hd := completedReductionTower Y d ⋙ completedTowerPullback g d ⋙
    pbcTowerEvaluation X (pbcAdicCompletion X d) a
  let α : Hc ⟶ completedReductionFiniteTarget g d a ⋙ pbcDerivedRestrict πa :=
    restrictedTransition (completedReductionFiniteEvaluation g d b).hom
      (completedReductionTargetTransition g d a b h) e
  let β : Hc ⟶ completedReductionFiniteTarget g d a ⋙ pbcDerivedRestrict πa :=
    whiskeredComparison (completedReductionTower Y d) (completedTowerPullback g d)
      (pbcTowerTransition X (pbcAdicCompletion X d) b a h)
      (completedReductionFiniteEvaluation g d a).hom
  have ha := (completedReductionTargetTransition_exists g d a b h).exists.choose_spec
  have hb := (completedReductionFiniteEvaluation_exists g d b).exists.choose_spec
  have hc := (completedReductionFiniteEvaluation_exists g d a).exists.choose_spec
  change HasCompletedReductionTargetTransitionNormalization g d a b h
    (completedReductionTargetTransition g d a b h) at ha
  change HasCompletedReductionFiniteEvaluationNormalization g d b
    (completedReductionFiniteEvaluation g d b) at hb
  change HasCompletedReductionFiniteEvaluationNormalization g d a
    (completedReductionFiniteEvaluation g d a) at hc
  unfold HasCompletedReductionTargetTransitionNormalization
    completedReductionTransitionNormalized at ha
  unfold HasCompletedReductionFiniteEvaluationNormalization
    completedReductionComparisonNormalized at hb hc
  have hs := normalized_evaluation_square
    (DerivedCategory.Q (C := pbcModules Y (pbcAdicCompletion Y d))) Fa Fb Fc Fd
    (DerivedCategory.Q (C := pbcModules X (reductionCoefficient X d a)))
    (DerivedCategory.Q (C := pbcModules X (reductionCoefficient X d b)))
    (DerivedCategory.Q (C := pbcModules X (pbcAdicCompletion X d)))
    (completedReductionFiniteTarget g d a) (completedReductionFiniteTarget g d b) Hc Hd
    ((pbcRestrict q).mapHomologicalComplex (.up ℤ))
    ((pbcRestrict πb).mapHomologicalComplex (.up ℤ))
    ((pbcRestrict πa).mapHomologicalComplex (.up ℤ))
    (pbcDerivedRestrict q) (pbcDerivedRestrict πb) (pbcDerivedRestrict πa)
    (completedReductionRestrictionFactors X q) (completedReductionRestrictionFactors X πb)
    (completedReductionRestrictionFactors X πa) e
    (fun P ↦ (completedReductionFiniteModelNat g d a).app P)
    (fun P ↦ (completedReductionFiniteModelNat g d b).app P)
    (fun P ↦ (completedReductionPulledModelNat g d b).app P)
    (fun P ↦ (completedReductionPulledModelNat g d a).app P)
    (completedReductionTargetTransition g d a b h)
    (completedReductionFiniteEvaluation g d b).hom
    (completedReductionFiniteEvaluation g d a).hom
    (fun P ↦ (pbcTowerTransition X (pbcAdicCompletion X d) b a h).app
      ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj
        (DerivedCategory.Q.obj P))))
    (fun P ↦ (NatTrans.mapHomologicalComplex
      (completedReductionOrdinaryTransition g d a b h) (.up ℤ)).app P)
    (fun P ↦ (NatTrans.mapHomologicalComplex
      (completedReductionOrdinaryComparison g d b).hom (.up ℤ)).app P)
    (fun P ↦ (NatTrans.mapHomologicalComplex
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).map
        (homOfLE h).op) (.up ℤ)).app
          ((G.mapHomologicalComplex (.up ℤ)).obj ((H.mapHomologicalComplex (.up ℤ)).obj P)))
    (fun P ↦ (NatTrans.mapHomologicalComplex
      (completedReductionOrdinaryComparison g d a).hom (.up ℤ)).app P)
    (fun P ↦ DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (pbcRestrictComp πb q πa (completedReductionProjection_comp X d b a h)).hom
      (.up ℤ)).app (Fa.obj P)))
    (CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d)) ha hb hc
    (fun P ↦ mapComplex_square H G (V b) (V a) Eb Gb Ea Ga
      (pbcRestrict πb) (pbcRestrict q) (pbcRestrict πa)
      (completedReductionOrdinaryComparison g d b).hom
      (completedReductionOrdinaryComparison g d a).hom
      (completedReductionOrdinaryTransition g d a b h)
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).map
        (homOfLE h).op)
      (pbcRestrictComp πb q πa (completedReductionProjection_comp X d b a h))
      (fun M ↦ ordinary_finite_quotient_comparison g d M a b h) DerivedCategory.Q P)
    (fun P ↦ by
      simpa only [completedReductionPulledModelNat_app] using
        (pulledModel_transition g d P a b h))
    (fun P ↦ derivedRestrictionComp_factors πb q πa
      (completedReductionProjection_comp X d b a h) (Fa.obj P))
    (fun P hP ↦ by
      rw [completedReductionFiniteModelNat_app]
      have := finiteModel_isIso g d a P hP
      infer_instance)
  suffices α = β by
    simpa only [α, β, restrictedTransition_app, whiskeredComparison_app] using congr_app this K
  refine derived_natTrans_ext _ _
    (CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d))
    ?_ α β ?_
  · intro C
    let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
    obtain ⟨P, p, hP, _, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
        (R := pbcAdicCompletion Y d) C
    exact ⟨P, p, hP, hp⟩
  · intro P hP
    simpa only [α, β, whiskeredComparison_app] using hs P hP

end AlgebraicGeometry.Scheme
