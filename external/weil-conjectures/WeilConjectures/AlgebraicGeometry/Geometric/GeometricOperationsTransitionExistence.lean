/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometry.SemilinearGeometryOps
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-! # Compatibility of geometric operation transitions

Source: Zheng Construction 4.1 and Lemma 4.10.
(blueprint: lem-coef-semilinear-geometric-operations-transition-existence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] WeilConjectures.SemilinearSections.hasDerived
  HasDerivedCategory.standard
universe c v r
open CategoryTheory CategoryTheory.Limits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem localization_composite_transition_fac
    {C X Y : Type*} [Category C] [Category X] [Category Y]
    [Abelian C] [Abelian X] [Abelian Y]
    [HasDerivedCategory C] [HasDerivedCategory X] [HasDerivedCategory Y]
    (E₀ : C ⥤ X) (E₁ : C ⥤ Y) (p : Y ⥤ X)
    [E₀.Additive] [E₁.Additive] [p.Additive]
    [PreservesFiniteLimits E₀] [PreservesFiniteColimits E₀]
    [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
    [PreservesFiniteLimits p] [PreservesFiniteColimits p]
    (τ : E₀ ⟶ E₁ ⋙ p) (K : CochainComplex C ℤ) :
    ((Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ)) _ _
      E₀.mapDerivedCategory (E₁ ⋙ p).mapDerivedCategory
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (.up ℤ))
        DerivedCategory.Q)) ≫ (Functor.mapDerivedCategoryCompIso E₁ p).inv).app
          (DerivedCategory.Q.obj K) ≫
        p.mapDerivedCategory.map (E₁.mapDerivedCategoryFactors.hom.app K) ≫
        p.mapDerivedCategoryFactors.hom.app ((E₁.mapHomologicalComplex (.up ℤ)).obj K) =
      E₀.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) := by
  dsimp only [NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Localization.liftNatTrans_app]
  simp only [Category.assoc]
  change _ ≫ _ ≫ (E₁ ⋙ p).mapDerivedCategoryFactors.inv.app K ≫ _ = _
  simp only [Iso.inv_hom_id_app, Category.comp_id]
  rfl

private theorem localize_transition
    {C D X₀ X₁ Y₀ Y₁ : Type*}
    [Category C] [Category D] [Category X₀] [Category X₁] [Category Y₀] [Category Y₁]
    [Abelian C] [Abelian D] [Abelian X₀] [Abelian X₁] [Abelian Y₀] [Abelian Y₁]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory X₀] [HasDerivedCategory X₁]
    [HasDerivedCategory Y₀] [HasDerivedCategory Y₁]
    (U : C ⥤ D) (E₀ : C ⥤ X₀) (E₁ : C ⥤ X₁)
    (B₀ : D ⥤ Y₀) (B₁ : D ⥤ Y₁) (F₀ : X₀ ⥤ Y₀) (F₁ : X₁ ⥤ Y₁)
    (p : X₁ ⥤ X₀) (q : Y₁ ⥤ Y₀)
    [U.Additive] [E₀.Additive] [E₁.Additive] [B₀.Additive] [B₁.Additive]
    [F₀.Additive] [F₁.Additive] [p.Additive] [q.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits E₀] [PreservesFiniteColimits E₀]
    [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
    [PreservesFiniteLimits B₀] [PreservesFiniteColimits B₀]
    [PreservesFiniteLimits B₁] [PreservesFiniteColimits B₁]
    [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits p] [PreservesFiniteColimits p]
    [PreservesFiniteLimits q] [PreservesFiniteColimits q]
    (α₀ : U ⋙ B₀ ≅ E₀ ⋙ F₀) (α₁ : U ⋙ B₁ ≅ E₁ ⋙ F₁)
    (γ : p ⋙ F₀ ≅ F₁ ⋙ q) (τ : E₀ ⟶ E₁ ⋙ p) (σ : B₀ ⟶ B₁ ⋙ q)
    (t : E₀.mapDerivedCategory ⟶ E₁.mapDerivedCategory ⋙ p.mapDerivedCategory)
    (s : B₀.mapDerivedCategory ⟶ B₁.mapDerivedCategory ⋙ q.mapDerivedCategory)
    (tfac : ∀ K : CochainComplex C ℤ,
      t.app (DerivedCategory.Q.obj K) ≫
        p.mapDerivedCategory.map (E₁.mapDerivedCategoryFactors.hom.app K) ≫
        p.mapDerivedCategoryFactors.hom.app ((E₁.mapHomologicalComplex (.up ℤ)).obj K) =
      E₀.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K))
    (sfac : ∀ K : CochainComplex D ℤ,
      s.app (DerivedCategory.Q.obj K) ≫
        q.mapDerivedCategory.map (B₁.mapDerivedCategoryFactors.hom.app K) ≫
        q.mapDerivedCategoryFactors.hom.app ((B₁.mapHomologicalComplex (.up ℤ)).obj K) =
      B₀.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex σ (.up ℤ)).app K))
    (htord : ∀ M, σ.app (U.obj M) ≫ q.map (α₁.hom.app M) =
      α₀.hom.app M ≫ F₀.map (τ.app M) ≫ γ.hom.app (E₁.obj M))
    (M : DerivedCategory C) :
    s.app (U.mapDerivedCategory.obj M) ≫
        q.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso α₁).hom.app M) =
      (Functor.mapDerivedCategorySquareIso α₀).hom.app M ≫
        F₀.mapDerivedCategory.map (t.app M) ≫
        (Functor.mapDerivedCategorySquareIso γ).hom.app (E₁.mapDerivedCategory.obj M) := by
  let a₀ := Functor.mapDerivedCategorySquareIso α₀
  let a₁ := Functor.mapDerivedCategorySquareIso α₁
  let β := Functor.mapDerivedCategorySquareIso γ
  let l : U.mapDerivedCategory ⋙ B₀.mapDerivedCategory ⟶
      (E₁.mapDerivedCategory ⋙ F₁.mapDerivedCategory) ⋙ q.mapDerivedCategory :=
    Functor.whiskerLeft U.mapDerivedCategory s ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight a₁.hom q.mapDerivedCategory
  let r : U.mapDerivedCategory ⋙ B₀.mapDerivedCategory ⟶
      (E₁.mapDerivedCategory ⋙ F₁.mapDerivedCategory) ⋙ q.mapDerivedCategory :=
    a₀.hom ≫ Functor.whiskerRight t F₀.mapDerivedCategory ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft E₁.mapDerivedCategory β.hom ≫ (Functor.associator _ _ _).inv
  have hlr : l = r := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
    intro K
    dsimp only [l, r, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id]
    let K₁ := (E₁.mapHomologicalComplex (.up ℤ)).obj K
    let UK := (U.mapHomologicalComplex (.up ℤ)).obj K
    have ha₀ := Functor.exactSquare_fac α₀ K
    have ha₁ := Functor.exactSquare_fac α₁ K
    have hβ := Functor.exactSquare_fac γ K₁
    have ht := tfac K
    have hs := sfac UK
    apply (cancel_mono
      (q.mapDerivedCategory.map
          (F₁.mapDerivedCategory.map (E₁.mapDerivedCategoryFactors.hom.app K)) ≫
        q.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K₁) ≫
        q.mapDerivedCategoryFactors.hom.app
          ((F₁.mapHomologicalComplex (.up ℤ)).obj K₁))).1
    simp only [Category.assoc]
    have hnβ := β.hom.naturality (E₁.mapDerivedCategoryFactors.hom.app K)
    dsimp only [Functor.comp_map] at hnβ
    erw [← reassoc_of% hnβ, hβ]
    rw [← F₀.mapDerivedCategory.map_comp_assoc,
      ← F₀.mapDerivedCategory.map_comp_assoc, Category.assoc]
    erw [ht]
    simp only [Functor.map_comp, Category.assoc]
    have hnF := F₀.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K)
    dsimp only [Functor.comp_map] at hnF
    erw [reassoc_of% hnF]
    erw [reassoc_of% ha₀]
    rw [← q.mapDerivedCategory.map_comp_assoc,
      ← q.mapDerivedCategory.map_comp_assoc, Category.assoc]
    erw [ha₁]
    simp only [Functor.map_comp, Category.assoc]
    have hnq := q.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex α₁.hom (.up ℤ)).app K)
    dsimp only [Functor.comp_map] at hnq
    erw [hnq]
    have hns := s.naturality (U.mapDerivedCategoryFactors.hom.app K)
    dsimp only [Functor.comp_map] at hns
    erw [← reassoc_of% hns, reassoc_of% hs]
    have hord :
        (NatTrans.mapHomologicalComplex σ (.up ℤ)).app UK ≫
          (q.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex α₁.hom (.up ℤ)).app K) =
        (NatTrans.mapHomologicalComplex α₀.hom (.up ℤ)).app K ≫
          (F₀.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) ≫
          (NatTrans.mapHomologicalComplex γ.hom (.up ℤ)).app K₁ := by
      ext i
      exact htord (K.X i)
    simpa only [Functor.map_comp, Category.assoc] using congrArg
      (fun f ↦ B₀.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app K) ≫
        B₀.mapDerivedCategoryFactors.hom.app UK ≫ DerivedCategory.Q.map f) hord
  simpa only [l, r, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using NatTrans.congr_app hlr M

private theorem scalar_transition
    {X₀ X₁ Y₀ Y₁ : Type*}
    [Category X₀] [Category X₁] [Category Y₀] [Category Y₁]
    {T : X₀ ⥤ X₁} {p : X₁ ⥤ X₀} {S : Y₀ ⥤ Y₁} {q : Y₁ ⥤ Y₀}
    {F₀ : X₀ ⥤ Y₀} {F₁ : X₁ ⥤ Y₁}
    (t : T ⊣ p) (s : S ⊣ q) (χ : T ⋙ F₁ ≅ F₀ ⋙ S)
    (β : p ⋙ F₀ ≅ F₁ ⋙ q)
    (hχ : ∀ P, (s.homEquiv _ _) (χ.inv.app P) =
      F₀.map (t.unit.app P) ≫ β.hom.app (T.obj P))
    {P₀ : X₀} {P₁ : X₁} {Q₀ : Y₀} {Q₁ : Y₁}
    (a₀ : Q₀ ⟶ F₀.obj P₀) (a₁ : Q₁ ⟶ F₁.obj P₁)
    (τ : P₀ ⟶ p.obj P₁) (σ : Q₀ ⟶ q.obj Q₁)
    (ht : σ ≫ q.map a₁ = a₀ ≫ F₀.map τ ≫ β.hom.app P₁) :
    (s.homEquiv _ _).symm σ ≫ a₁ =
      S.map a₀ ≫ χ.inv.app P₀ ≫ F₁.map ((t.homEquiv _ _).symm τ) := by
  apply (s.homEquiv _ _).injective
  rw [s.homEquiv_naturality_right, s.homEquiv_naturality_left,
    s.homEquiv_naturality_right, Equiv.apply_symm_apply, hχ]
  have hn := β.hom.naturality ((t.homEquiv _ _).symm τ)
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn, ← F₀.map_comp_assoc]
  have hu : t.unit.app P₀ ≫ p.map ((t.homEquiv _ _).symm τ) = τ := by
    simpa only [t.homEquiv_unit] using (t.homEquiv P₀ P₁).apply_symm_apply τ
  rw [hu]
  exact ht

namespace WeilConjectures.SemilinearSections

private theorem derived_transition_fac
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{max c v r} C]
    (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
    {m n : ℕ} (h : n ≤ m)
    (K : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) :
    (derivedTransition.{c, v, max c v r} J B τ h).app (DerivedCategory.Q.obj K) ≫
      (resD.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)).map
        ((Functor.mapDerivedCategoryFactors (evaluation.{c, v, max c v r} J B τ n)).hom.app K) ≫
      (Functor.mapDerivedCategoryFactors
        (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h))).hom.app
        (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj K) =
    (evaluation.{c, v, max c v r} J B τ m).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (transition.{c, v, max c v r} J B τ h) (.up ℤ)).app K) := by
  dsimp only [derivedTransition, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Localization.liftNatTrans_app]
  simp only [Category.assoc]
  change _ ≫ _ ≫
    (Functor.mapDerivedCategoryFactors
      (evaluation.{c, v, max c v r} J B τ n ⋙
        res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h))).inv.app K ≫ _ = _
  simp only [Iso.inv_hom_id_app, Category.comp_id]
  rfl

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

-- Elaborating the exact localization square compares several dependent derived categories.
private theorem pull_transition
    (A : Data.{c, v, r} J B τ)
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush)
    (G : Geometry.{c, v, r} J B τ A J' uInv uPush adjSet)
    {m n : ℕ} (h : n ≤ m)
    (M : DS.{c, v, max c v r} J B τ) :
    (derivedTransition.{c, v, max c v r} J'
      G.coefficients G.coefficientTransition h).app
        (G.pull.mapDerivedCategory.obj M) ≫
      (resD.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J'
        G.coefficients G.coefficientTransition h)).map ((G.pullEvaluation n).hom.app M) =
    (G.pullEvaluation m).hom.app M ≫
      (G.inverseImage m).modules.mapDerivedCategory.map
        ((derivedTransition.{c, v, max c v r} J B τ h).app M) ≫
      ((Functor.mapDerivedCategoryCompIso _ _) ≪≫
        Functor.mapDerivedCategoryNatIso (G.restrictionPullback h) ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app
        ((e.{c, v, max c v r} J B τ n).obj M) := by
  rw [G.pullEvaluation_model n, G.pullEvaluation_model m]
  refine localize_transition
    (C := Systems.{c, v, max c v r} J B τ)
    (D := Systems.{c, v, max c v r} J' G.coefficients G.coefficientTransition)
    (X₀ := Mod.{c, v, max c v r} J (B m))
    (X₁ := Mod.{c, v, max c v r} J (B n))
    (Y₀ := Mod.{c, v, max c v r} J' (G.coefficients m))
    (Y₁ := Mod.{c, v, max c v r} J' (G.coefficients n)) G.pull
    (evaluation.{c, v, max c v r} J B τ m)
    (evaluation.{c, v, max c v r} J B τ n)
    (evaluation.{c, v, max c v r} J'
      G.coefficients G.coefficientTransition m)
    (evaluation.{c, v, max c v r} J'
      G.coefficients G.coefficientTransition n)
    (G.inverseImage m).modules (G.inverseImage n).modules
    (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r}
      J B τ h))
    (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r}
      J' G.coefficients G.coefficientTransition h))
    (G.ordinaryPullEvaluation m) (G.ordinaryPullEvaluation n) (G.restrictionPullback h)
    (transition.{c, v, max c v r} J B τ h)
    (transition.{c, v, max c v r} J'
      G.coefficients G.coefficientTransition h)
    (derivedTransition.{c, v, max c v r} J B τ h)
    (derivedTransition.{c, v, max c v r} J'
      G.coefficients G.coefficientTransition h)
    ?_ ?_ ?_ M
  · intro K
    exact localization_composite_transition_fac _ _ _
      (transition.{c, v, max c v r} J B τ h) K
  · intro K
    exact localization_composite_transition_fac _ _ _
      (transition.{c, v, max c v r} J' G.coefficients G.coefficientTransition h) K
  · exact G.ordinaryPullTransition h

/-- The canonical termwise construction satisfies the pull-transition equation.  On each
coefficient level this is the mate identity for inverse image and direct image; the ordinary
coefficient tensor comparison and its inverse give the displayed system equation. -/
theorem semilinearGeometryTransitionExistence (systems : Data.{c, v, r} J B τ)
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (G : Geometry.{c, v, r} J B τ systems J' uInv uPush adjSet) :
    G.PullTransitionFormula J B τ systems J' uInv uPush adjSet := by
  intro m n h M
  exact scalar_transition (systems.scalar h).adjunction (G.target.scalar h).adjunction
    (G.coefficientPullback h)
    ((Functor.mapDerivedCategoryCompIso _ _) ≪≫
      Functor.mapDerivedCategoryNatIso (G.restrictionPullback h) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm)
    (G.coefficientPullback_transpose h)
    ((G.pullEvaluation m).hom.app M) ((G.pullEvaluation n).hom.app M)
    ((derivedTransition.{c, v, max c v r} J B τ h).app M)
    ((derivedTransition.{c, v, max c v r} J' G.coefficients G.coefficientTransition h).app
      (G.pull.mapDerivedCategory.obj M))
    (pull_transition J B τ systems J' uInv uPush adjSet G h M)

end WeilConjectures.SemilinearSections
