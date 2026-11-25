/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryEvaluationComparisons
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryModuleComposition
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryOpenUnit
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-!
# Normalization of the ordinary realization comparisons

Source: Zheng, Construction 4.1; Stacks Project, Tags 03DI and 09AE.
(blueprint: lem-sp-varying-ring-ordinary-comparison-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
attribute [local instance 2000] WeilConjectures.SemilinearSections.sequenceSmall
  StrictTower.towers_hasDerivedCategory Scheme.proEtaleRingModules_hasDerivedCategory

attribute [local irreducible] ordinaryRealization moduleGComp moduleJComp
  StrictTower.gComp StrictTower.jComp Functor.leftAdjoint
  Functor.mapDerivedCategory StrictTower.towers_hasDerivedCategory
  Scheme.proEtaleRingModules_hasDerivedCategory

section CompositionPredicate
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  {L₀ : C₀ ⥤ C₁} {L₁ : C₁ ⥤ C₂} {L₂ : C₀ ⥤ C₂}
  {M₀ : D₀ ⥤ D₁} {M₁ : D₁ ⥤ D₂} {M₂ : D₀ ⥤ D₂}
  {V₀ : C₀ ⥤ D₀} {V₁ : C₁ ⥤ D₁} {V₂ : C₂ ⥤ D₂}

-- Package the equation before specializing to large scheme-site categories.
private def ComparisonComposition
    (a₀ : L₀ ⋙ V₁ ≅ V₀ ⋙ M₀) (a₁ : L₁ ⋙ V₂ ≅ V₁ ⋙ M₁)
    (a₂ : L₂ ⋙ V₂ ≅ V₀ ⋙ M₂)
    (c : L₂ ≅ L₀ ⋙ L₁) (d : M₂ ≅ M₀ ⋙ M₁) : Prop :=
  ∀ x : C₀, V₂.map (c.hom.app x) ≫ a₁.hom.app (L₀.obj x) ≫
    M₁.map (a₀.hom.app x) = a₂.hom.app x ≫ d.hom.app (V₀.obj x)

end CompositionPredicate

section SingleComposition
variable {A B C : Type*} [Category A] [Category B] [Category C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

private theorem single_comp (e : H ≅ F ⋙ G) (M : A) :
    (DerivedCategory.singleFunctor C 0).map (e.hom.app M) ≫
      (G.mapDerivedCategorySingleFunctor 0).inv.app (F.obj M) ≫
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).inv.app M) =
    (H.mapDerivedCategorySingleFunctor 0).inv.app M ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      (Functor.mapDerivedCategoryCompIso F G).inv.app _ := by
  apply (cancel_epi ((H.mapDerivedCategorySingleFunctor 0).hom.app M)).1
  rw [← Category.assoc, ← Functor.mapDerivedCategoryNatIso_comp_hom_app_singleFunctor
    F G H e M]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  erw [G.mapDerivedCategory.map_id, Category.comp_id]

end SingleComposition

section ConstantComposition
variable {A B C : Type*} [Category A] [Category B] [Category C]
  (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)

private theorem const_comp (e : H ≅ F ⋙ G) (M : A) :
    (Functor.const ℕᵒᵖ).map (e.hom.app M) ≫
      (Functor.compConstIso ℕᵒᵖ G).hom.app (F.obj M) ≫
      ((Functor.whiskeringRight ℕᵒᵖ B C).obj G).map
        ((Functor.compConstIso ℕᵒᵖ F).hom.app M) =
    (Functor.compConstIso ℕᵒᵖ H).hom.app M ≫
      (((Functor.whiskeringRight ℕᵒᵖ A C).mapIso e) ≪≫
        Functor.whiskeringRightObjCompIso F G).hom.app ((Functor.const ℕᵒᵖ).obj M) := by
  ext j
  simp

variable [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory (ℕᵒᵖ ⥤ C)]
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B C).obj G)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B C).obj G)]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A C).obj H)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A C).obj H)]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A C).obj (F ⋙ G))]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A C).obj (F ⋙ G))]

private theorem constantSingle_comp (e : H ≅ F ⋙ G) :
    ComparisonComposition (ordinaryConstantSingleComparison F)
      (ordinaryConstantSingleComparison G) (ordinaryConstantSingleComparison H) e
      (Functor.mapDerivedCategoryNatIso
        (((Functor.whiskeringRight ℕᵒᵖ A C).mapIso e) ≪≫
          Functor.whiskeringRightObjCompIso F G) ≪≫
        (Functor.mapDerivedCategoryCompIso
          ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)
          ((Functor.whiskeringRight ℕᵒᵖ B C).obj G)).symm) := by
  intro M
  dsimp only [Iso.trans_hom, NatTrans.comp_app]
  simp only [ordinaryConstantSingleComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
  let F' := (Functor.whiskeringRight ℕᵒᵖ A B).obj F
  let G' := (Functor.whiskeringRight ℕᵒᵖ B C).obj G
  let H' := (Functor.whiskeringRight ℕᵒᵖ A C).obj H
  let K := (Functor.const ℕᵒᵖ).obj M
  have hn := (G'.mapDerivedCategorySingleFunctor 0).inv.naturality
    ((Functor.compConstIso ℕᵒᵖ F).hom.app M)
  have hs := single_comp F' G' H'
    (((Functor.whiskeringRight ℕᵒᵖ A C).mapIso e) ≪≫
      Functor.whiskeringRightObjCompIso F G) K
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Functor.comp_map, Functor.map_comp]
  rw [← reassoc_of% hn]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
    const_comp F G H e M]
  rw [Functor.map_comp, Category.assoc, hs]
  rfl

end ConstantComposition

section PasteComparison
variable {A B C D E F : Type*}
  [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
  {L₁ : A ⥤ B} {G : A ⥤ C} {H : B ⥤ D} {L₂ : C ⥤ D}
  {I : C ⥤ E} {J : D ⥤ F} {L₃ : E ⥤ F} {EA : A ⥤ E} {EB : B ⥤ F}

private def pasteComparison (α : L₁ ⋙ H ≅ G ⋙ L₂) (β : L₂ ⋙ J ≅ I ⋙ L₃)
    (eA : EA ≅ G ⋙ I) (eB : EB ≅ H ⋙ J) : L₁ ⋙ EB ≅ EA ⋙ L₃ :=
  Functor.isoWhiskerLeft _ eB ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight α _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ β ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eA.symm _

end PasteComparison

private theorem comparison_eq (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryPullComparison R φ n X Y f =
      pasteComparison (moduleEvalG R φ f n)
        (ordinaryConstantSingleComparison (StrictTower.modulePullback (R n) f))
        (eqToIso (ordinaryRealization_eq R φ n Y))
        (eqToIso (ordinaryRealization_eq R φ n X)) := by
  rfl

section PasteComposition
variable {C₀ C₁ C₂ D₀ D₁ D₂ E₀ E₁ E₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  [Category E₀] [Category E₁] [Category E₂]
  {L₀ : C₀ ⥤ C₁} {L₁ : C₁ ⥤ C₂} {L₂ : C₀ ⥤ C₂}
  {M₀ : D₀ ⥤ D₁} {M₁ : D₁ ⥤ D₂} {M₂ : D₀ ⥤ D₂}
  {N₀ : E₀ ⥤ E₁} {N₁ : E₁ ⥤ E₂} {N₂ : E₀ ⥤ E₂}
  {V₀ : C₀ ⥤ D₀} {V₁ : C₁ ⥤ D₁} {V₂ : C₂ ⥤ D₂}
  {W₀ : D₀ ⥤ E₀} {W₁ : D₁ ⥤ E₁} {W₂ : D₂ ⥤ E₂}
  {T₀ : C₀ ⥤ E₀} {T₁ : C₁ ⥤ E₁} {T₂ : C₂ ⥤ E₂}

private theorem paste_comp
    (a₀ : L₀ ⋙ V₁ ≅ V₀ ⋙ M₀) (a₁ : L₁ ⋙ V₂ ≅ V₁ ⋙ M₁)
    (a₂ : L₂ ⋙ V₂ ≅ V₀ ⋙ M₂)
    (b₀ : M₀ ⋙ W₁ ≅ W₀ ⋙ N₀) (b₁ : M₁ ⋙ W₂ ≅ W₁ ⋙ N₁)
    (b₂ : M₂ ⋙ W₂ ≅ W₀ ⋙ N₂)
    (c : L₂ ≅ L₀ ⋙ L₁) (d : M₂ ≅ M₀ ⋙ M₁) (e : N₂ ≅ N₀ ⋙ N₁)
    (t₀ : T₀ ≅ V₀ ⋙ W₀) (t₁ : T₁ ≅ V₁ ⋙ W₁) (t₂ : T₂ ≅ V₂ ⋙ W₂)
    (h₀ : ComparisonComposition a₀ a₁ a₂ c d)
    (h₁ : ComparisonComposition b₀ b₁ b₂ d e) :
    ComparisonComposition (pasteComparison a₀ b₀ t₀ t₁)
      (pasteComparison a₁ b₁ t₁ t₂) (pasteComparison a₂ b₂ t₀ t₂) c e := by
  intro x
  have ht := t₂.hom.naturality (c.hom.app x)
  have hb := b₁.hom.naturality (a₀.hom.app x)
  have he := e.hom.naturality (t₀.inv.app x)
  dsimp only [Functor.comp_map, Functor.comp_obj] at ht hb he
  simp only [pasteComparison, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Functor.map_comp, Category.assoc]
  rw [reassoc_of% ht]
  simp only [← N₁.map_comp_assoc]
  simp only [Iso.inv_hom_id_app_assoc, N₁.map_comp, Category.assoc]
  rw [← reassoc_of% hb]
  rw [← W₂.map_comp_assoc, ← W₂.map_comp_assoc, Category.assoc, h₀ x]
  simp only [W₂.map_comp, Category.assoc]
  rw [reassoc_of% h₁ (V₀.obj x), he]

end PasteComposition

attribute [local semireducible] StrictTower.gComp

private theorem tower_comp (n : ℕ) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ComparisonComposition
      (ordinaryConstantSingleComparison (StrictTower.modulePullback (R n) g))
      (ordinaryConstantSingleComparison (StrictTower.modulePullback (R n) f))
      (ordinaryConstantSingleComparison (StrictTower.modulePullback (R n) (f ≫ g)))
      (StrictTower.moduleGComp (R n) f g) (StrictTower.gComp (R n) f g) := by
  have : PreservesFiniteLimits
      ((Functor.whiskeringRight ℕᵒᵖ (StrictTower.Modules (R n) Z)
        (StrictTower.Modules (R n) X)).obj
          (StrictTower.modulePullback (R n) g ⋙ StrictTower.modulePullback (R n) f)) := by
    change PreservesFiniteLimits
      (StrictTower.towerPullback (R n) g ⋙ StrictTower.towerPullback (R n) f)
    exact comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits
      ((Functor.whiskeringRight ℕᵒᵖ (StrictTower.Modules (R n) Z)
        (StrictTower.Modules (R n) X)).obj
          (StrictTower.modulePullback (R n) g ⋙ StrictTower.modulePullback (R n) f)) := by
    change PreservesFiniteColimits
      (StrictTower.towerPullback (R n) g ⋙ StrictTower.towerPullback (R n) f)
    exact comp_preservesFiniteColimits _ _
  exact constantSingle_comp (StrictTower.modulePullback (R n) g)
    (StrictTower.modulePullback (R n) f) (StrictTower.modulePullback (R n) (f ≫ g))
    (StrictTower.moduleGComp (R n) f g)

attribute [local irreducible] StrictTower.gComp

private theorem pull_composition (n : ℕ) :
    OrdinaryPullComposition R φ n (ordinaryPullComparison R φ n) := by
  intro X Y Z f g
  change ComparisonComposition (ordinaryPullComparison R φ n Y Z g)
    (ordinaryPullComparison R φ n X Y f) (ordinaryPullComparison R φ n X Z (f ≫ g))
    (moduleGComp R φ f g) (StrictTower.gComp (R n) f g)
  rw [comparison_eq, comparison_eq, comparison_eq]
  apply paste_comp (moduleEvalG R φ g n) (moduleEvalG R φ f n)
    (moduleEvalG R φ (f ≫ g) n)
    (ordinaryConstantSingleComparison (StrictTower.modulePullback (R n) g))
    (ordinaryConstantSingleComparison (StrictTower.modulePullback (R n) f))
    (ordinaryConstantSingleComparison (StrictTower.modulePullback (R n) (f ≫ g)))
    (moduleGComp R φ f g) (StrictTower.moduleGComp (R n) f g)
    (StrictTower.gComp (R n) f g)
    (eqToIso (ordinaryRealization_eq R φ n Z))
    (eqToIso (ordinaryRealization_eq R φ n Y))
    (eqToIso (ordinaryRealization_eq R φ n X))
  · exact ordinaryModuleEvalG_comp R φ n f g
  · exact tower_comp R n f g

attribute [local irreducible] ordinaryPullComparison ordinaryOpenComparison
  StrictTower.G StrictTower.J

private lemma mateSquare
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    {L₃ L₄ : E ⥤ F} {R₃ R₄ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (q : TwoSquare G L₁ L₃ H) (r : TwoSquare G L₂ L₄ H)
    (s : L₄ ⟶ L₃) (t : L₂ ⟶ L₁)
    (h : (mateEquiv a₁ a₃ q).whiskerBottom (conjugateEquiv a₃ a₄ s) =
      (mateEquiv a₂ a₄ r).whiskerTop (conjugateEquiv a₁ a₂ t)) :
    q.whiskerRight s = r.whiskerLeft t := by
  apply (mateEquiv a₁ a₄).injective
  rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp]
  exact h

section MateComposition
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  {L₀ : C₀ ⥤ C₁} {L₁ : C₁ ⥤ C₂} {L₂ : C₀ ⥤ C₂}
  {R₀ : C₁ ⥤ C₀} {R₁ : C₂ ⥤ C₁} {R₂ : C₂ ⥤ C₀}
  {l₀ : D₀ ⥤ D₁} {l₁ : D₁ ⥤ D₂} {l₂ : D₀ ⥤ D₂}
  {r₀ : D₁ ⥤ D₀} {r₁ : D₂ ⥤ D₁} {r₂ : D₂ ⥤ D₀}
  {E₀ : C₀ ⥤ D₀} {E₁ : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂}

private def OpenComparisonComposition
    (α₀ : L₀ ⋙ E₁ ≅ E₀ ⋙ l₀) (α₁ : L₁ ⋙ E₂ ≅ E₁ ⋙ l₁)
    (α₂ : L₂ ⋙ E₂ ≅ E₀ ⋙ l₂)
    (c : L₀ ⋙ L₁ ≅ L₂) (d : l₀ ⋙ l₁ ≅ l₂) : Prop :=
  ∀ N : C₀, E₂.map (c.hom.app N) ≫ α₂.hom.app N =
    α₁.hom.app (L₀.obj N) ≫ l₁.map (α₀.hom.app N) ≫ d.hom.app (E₀.obj N)

-- Keep the normalization propositions folded when specializing to scheme-site functors.
private theorem pull_mate_pasting
    (β₀ : R₀ ⋙ E₀ ≅ E₁ ⋙ r₀) (β₁ : R₁ ⋙ E₁ ≅ E₂ ⋙ r₁)
    (β₂ : R₂ ⋙ E₀ ≅ E₂ ⋙ r₂)
    (cR : R₂ ≅ R₁ ⋙ R₀) (dR : r₂ ≅ r₁ ⋙ r₀)
    (hp : ComparisonComposition β₁ β₀ β₂ cR dR) :
    ((TwoSquare.mk R₁ E₂ E₁ r₁ β₁.hom).hComp
      (TwoSquare.mk R₀ E₁ E₀ r₀ β₀.hom)).whiskerBottom dR.inv =
    (TwoSquare.mk R₂ E₂ E₀ r₂ β₂.hom).whiskerTop cR.inv := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  simp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id]
  apply (cancel_epi (E₀.map (cR.hom.app M))).1
  simp only [← E₀.map_comp_assoc, Iso.hom_inv_id_app, E₀.map_id, Category.id_comp]
  rw [← Category.assoc, hp M]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

private theorem open_from_inverse_pasting
    (α₀ : L₀ ⋙ E₁ ≅ E₀ ⋙ l₀) (α₁ : L₁ ⋙ E₂ ≅ E₁ ⋙ l₁)
    (α₂ : L₂ ⋙ E₂ ≅ E₀ ⋙ l₂)
    (c : L₀ ⋙ L₁ ≅ L₂) (d : l₀ ⋙ l₁ ≅ l₂)
    (hc : ((TwoSquare.mk E₀ L₀ l₀ E₁ α₀.inv).vComp
      (TwoSquare.mk E₁ L₁ l₁ E₂ α₁.inv)).whiskerRight d.inv =
      (TwoSquare.mk E₀ L₂ l₂ E₂ α₂.inv).whiskerLeft c.inv) :
    OpenComparisonComposition α₀ α₁ α₂ c d := by
  intro N
  have hm := congrArg (fun z ↦ z.app N) hc
  simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at hm
  let a := E₂.mapIso (c.app N) ≪≫ α₂.app N
  let b := α₁.app (L₀.obj N) ≪≫ l₁.mapIso (α₀.app N) ≪≫ d.app (E₀.obj N)
  have hi : a = b := by
    apply Iso.ext_inv
    simpa only [a, b, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
      Category.assoc] using hm.symm
  simpa only [a, b, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc] using congrArg Iso.hom hi

end MateComposition

attribute [local semireducible] moduleJComp StrictTower.jComp

private theorem module_conj {U V X : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    conjugateEquiv ((moduleJAdj R φ i).comp (moduleJAdj R φ j))
      (moduleJAdj R φ (i ≫ j)) (moduleJComp R φ i j).inv =
      (moduleGComp R φ i j).inv := by
  exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv
    (moduleJAdj R φ i) (moduleJAdj R φ j) (moduleJAdj R φ (i ≫ j))
    (moduleGComp R φ i j).symm

private theorem strict_conj (n : ℕ) {U V X : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    conjugateEquiv ((StrictTower.jAdj (R n) i).comp (StrictTower.jAdj (R n) j))
      (StrictTower.jAdj (R n) (i ≫ j)) (StrictTower.jComp (R n) i j).inv =
      (StrictTower.gComp (R n) i j).inv := by
  exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv
    (StrictTower.jAdj (R n) i) (StrictTower.jAdj (R n) j)
    (StrictTower.jAdj (R n) (i ≫ j)) (StrictTower.gComp (R n) i j).symm

private theorem open_composition (n : ℕ)
    (hp : OrdinaryPullComposition R φ n (ordinaryPullComparison R φ n)) :
    OrdinaryOpenComposition R φ n (ordinaryOpenComparison R φ n) := by
  intro U V X i j _ _
  apply open_from_inverse_pasting
    (ordinaryOpenComparison R φ n U V i) (ordinaryOpenComparison R φ n V X j)
    (ordinaryOpenComparison R φ n U X (i ≫ j))
    (moduleJComp R φ i j) (StrictTower.jComp (R n) i j)
  apply mateSquare ((moduleJAdj R φ i).comp (moduleJAdj R φ j))
    (moduleJAdj R φ (i ≫ j))
    ((StrictTower.jAdj (R n) i).comp (StrictTower.jAdj (R n) j))
    (StrictTower.jAdj (R n) (i ≫ j))
  rw [mateEquiv_hcomp, ordinaryOpen_mate, ordinaryOpen_mate, ordinaryOpen_mate,
    module_conj, strict_conj]
  exact pull_mate_pasting
    (ordinaryPullComparison R φ n U V i) (ordinaryPullComparison R φ n V X j)
    (ordinaryPullComparison R φ n U X (i ≫ j))
    (moduleGComp R φ i j) (StrictTower.gComp (R n) i j) (hp i j)

/-- The two construction normalizations, before any cartesian or section arrow.
Source: Zheng, Construction 4.1; Stacks 03DI and 09AE
(blueprint: lem-sp-varying-ring-ordinary-comparison-normalization).
Proof: use ordinaryRealization_eq to replace realization by its explicit
component/constant/single composite, keeping the equality transports. Apply
constant embedding and degree-zero embedding to ordinaryModuleEvalG_comp.
Naturality moves each evaluation comparison past its exact-single comparison;
the natural-isomorphism and compositor coherence of the exact-single comparison
identifies the remaining factors. Constant-tower comparison composes termwise.
This gives the specified pullback-composition equation.
For open composition first identify the mate of ordinaryOpenComparison.inv
with ordinaryPullComparison.hom. The defining inverse mate evalJInv of evalG
has this unit equation after localization. The fully faithful degree-zero
embedding recovers its ordinary version, constant embedding makes the unit
termwise, and the exact-single localization factors give the derived strict
unit. Whisker with evaluation and the realization equality isomorphisms.
Transpose the two inverse open-composition maps under the composite open
adjunctions. Mate pasting identifies their mates with the pullback-composition
maps just proved. Conjugation sends moduleJComp.inv and StrictTower.jComp.inv
to the corresponding inverse pullback compositors, by their leftAdjointCompIso
normalization. The pullback equation therefore makes the mates equal.
Injectivity of mateEquiv gives equality of inverse isomorphisms; inversion gives
the displayed forward open-composition equation. Neither calculation uses a
cartesian beta map or a clopen section projection. -/
theorem ordinaryComparisonNormalization (n : ℕ) :
    OrdinaryPullComposition R φ n (ordinaryPullComparison R φ n) ∧
      OrdinaryOpenComposition R φ n (ordinaryOpenComparison R φ n) := by
  exact ⟨pull_composition R φ n, open_composition R φ n (pull_composition R φ n)⟩

end AlgebraicGeometry.ProEtale.VaryingRing
