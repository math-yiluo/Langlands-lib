/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition
import WeilConjectures.AlgebraicGeometry.LowerStarPlusTransitionComp
import WeilConjectures.AlgebraicGeometry.BaseChangePullbackComparisonComp

/-! # Composition of target transitions

Source: the transition argument in Stacks Tag 0F07, thickening step.
(blueprint: lem-sbc-target-transition-comp)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry
variable (Λ : Type (u + 1)) [CommRing Λ]

private lemma lower_transition_naturality
    {X Y Y' : Scheme.{u}} (a : Y' ⟶ Y) (h : Y ⟶ X) (h' : Y' ⟶ X)
    (w : a ≫ h = h')
    {K L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (f : K ⟶ L) :
    R+((h)_*[ModuleCat.{u + 1} Λ]).map f ≫
        Etale.lowerStarPlusTransition Λ a h h' w L =
      Etale.lowerStarPlusTransition Λ a h h' w K ≫
        R+((h')_*[ModuleCat.{u + 1} Λ]).map
          (D+((a)^*[ModuleCat.{u + 1} Λ]).map f) := by
  let sq : CommSq a h' h (𝟙 X) := ⟨by rw [w, Category.comp_id]⟩
  have hn := ((Functor.whiskerLeft R+((h)_*[ModuleCat.{u + 1} Λ])
    (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv) ≫
      Etale.baseChange (ModuleCat.{u + 1} Λ) sq).naturality f
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_map,
    Functor.id_map] at hn
  rw [Etale.lowerStarPlusTransition_eq_baseChange Λ a h h' w sq K,
    Etale.lowerStarPlusTransition_eq_baseChange Λ a h h' w sq L]
  exact hn

private lemma transition_with_coefficients_comp
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (B : C ⥤ D) (R₂ : C ⥤ E) (R₁ : D ⥤ E)
    {K₂ L₂ : C} {K₁ M₁ N₁ : D} {P : E}
    (t₂ : P ⟶ R₂.obj K₂) (t₁ : R₂.obj K₂ ⟶ R₁.obj (B.obj K₂))
    (t₁' : R₂.obj L₂ ⟶ R₁.obj (B.obj L₂)) (t₀ : P ⟶ R₁.obj N₁)
    (c₂ : K₂ ⟶ L₂) (c₁ : B.obj L₂ ⟶ M₁) (v : M₁ ⟶ K₁)
    (d : B.obj K₂ ⟶ N₁) (c₀ : N₁ ⟶ K₁)
    (hn : R₂.map c₂ ≫ t₁' = t₁ ≫ R₁.map (B.map c₂))
    (ht : t₂ ≫ t₁ ≫ R₁.map d = t₀)
    (hc : B.map c₂ ≫ c₁ ≫ v = d ≫ c₀) :
    (t₂ ≫ R₂.map c₂) ≫ (t₁' ≫ R₁.map c₁) ≫ R₁.map v = t₀ ≫ R₁.map c₀ := by
  simp only [Category.assoc]
  rw [reassoc_of% hn, ← R₁.map_comp_assoc, ← R₁.map_comp, Category.assoc, hc, R₁.map_comp]
  simpa only [Category.assoc] using congrArg (· ≫ R₁.map c₀) ht

private lemma map_comp_three
    {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {K L M N : C} (f : K ⟶ L) (g : L ⟶ M) (k : M ⟶ N) (l : K ⟶ N)
    (h : f ≫ g ≫ k = l) : H.map f ≫ H.map g ≫ H.map k = H.map l := by
  rw [← H.map_comp, ← H.map_comp, h]

private lemma map_comp_with_coefficient
    {A B C D E : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E]
    (S : A ⥤ B) (U : B ⥤ C) (R : C ⥤ D) (H : D ⥤ E)
    {K L : A} {P Q : D} (f : P ⟶ Q) (g : Q ⟶ R.obj (U.obj (S.obj K)))
    (α : K ⟶ L) (l : P ⟶ R.obj (U.obj (S.obj L)))
    (h : f ≫ g ≫ R.map (U.map (S.map α)) = l) :
    H.map f ≫ H.map g ≫ (S ⋙ ((U ⋙ R) ⋙ H)).map α = H.map l := by
  exact map_comp_three H f g _ l h

private lemma target_transition_eq
    {X T Y T' Y' : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ)
    (π : T' ⟶ T) (a : Y' ⟶ Y) (e' : Y' ⟶ T') (h' : Y' ⟶ X)
    (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
    let c := (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app K ≫
      eqToHom (by rw [wa]) ≫
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e' π).hom.app K ≫
      D+((e')^*[ModuleCat.{u + 1} Λ]).map
        ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
    Etale.baseChangeTargetTransition Λ e h q π a e' h' wa wh F =
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (Etale.lowerStarPlusTransition Λ a h h' wh _ ≫
          R+((h')_*[ModuleCat.{u + 1} Λ]).map c) := rfl

/-- Target transitions compose, including the comparison of the coefficient pullbacks.

Source: Stacks Tag 0F07, proof of condition (1), and the definition of the canonical
restriction maps in Tag 09Z1. (blueprint: lem-sbc-target-transition-comp)

Proof: expand the transitions as derived units and counits. Paste the two degenerate
commutative squares using the generic mate-pasting law (which requires no cartesianness);
the triangle identities identify their composite
with the transition for the composite. The associativity of the pullback comparison
identifies the final coefficient with `(π₁ ≫ π₂)^* F`. Apply degree-q homology.
-/
theorem Etale.baseChangeTargetTransition_comp
    {X T Y T₁ T₂ Y₁ Y₂ : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ)
    (π₂ : T₂ ⟶ T) (a₂ : Y₂ ⟶ Y) (e₂ : Y₂ ⟶ T₂) (h₂ : Y₂ ⟶ X)
    (wa₂ : a₂ ≫ e = e₂ ≫ π₂) (wh₂ : a₂ ≫ h = h₂)
    (π₁ : T₁ ⟶ T₂) (a₁ : Y₁ ⟶ Y₂) (e₁ : Y₁ ⟶ T₁) (h₁ : Y₁ ⟶ X)
    (wa₁ : a₁ ≫ e₂ = e₁ ≫ π₁) (wh₁ : a₁ ≫ h₂ = h₁)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Etale.baseChangeTargetTransition Λ e h q π₂ a₂ e₂ h₂ wa₂ wh₂ F ≫
        Etale.baseChangeTargetTransition Λ e₂ h₂ q π₁ a₁ e₁ h₁ wa₁ wh₁
          (((π₂)^*[ModuleCat.{u + 1} Λ]).obj F) ≫
        (Etale.baseChangeTargetFunctor Λ e₁ h₁ q).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) π₁ π₂ (π₁ ≫ π₂) rfl).inv.app F) =
      Etale.baseChangeTargetTransition Λ e h q (π₁ ≫ π₂) (a₁ ≫ a₂) e₁ h₁
        (by rw [Category.assoc, wa₂, ← Category.assoc, wa₁, Category.assoc])
        (by rw [Category.assoc, wh₂, wh₁]) F := by
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let c₂ : D+((a₂)^*[ModuleCat.{u + 1} Λ]).obj
      (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ⟶
      D+((e₂)^*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (((π₂)^*[ModuleCat.{u + 1} Λ]).obj F)) :=
    (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₂ e).inv.app K ≫
    eqToHom (by rw [wa₂]) ≫
    (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e₂ π₂).hom.app K ≫
    D+((e₂)^*[ModuleCat.{u + 1} Λ]).map
      ((((π₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
  let c₁ : D+((a₁)^*[ModuleCat.{u + 1} Λ]).obj
      (D+((e₂)^*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (((π₂)^*[ModuleCat.{u + 1} Λ]).obj F))) ⟶
      D+((e₁)^*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (((π₁)^*[ModuleCat.{u + 1} Λ]).obj (((π₂)^*[ModuleCat.{u + 1} Λ]).obj F))) :=
    (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₁ e₂).inv.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (((π₂)^*[ModuleCat.{u + 1} Λ]).obj F)) ≫
    eqToHom (by rw [wa₁]) ≫
    (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e₁ π₁).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (((π₂)^*[ModuleCat.{u + 1} Λ]).obj F)) ≫
    D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
      ((((π₁)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        (((π₂)^*[ModuleCat.{u + 1} Λ]).obj F))
  let c₀ : D+((a₁ ≫ a₂)^*[ModuleCat.{u + 1} Λ]).obj
      (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ⟶
      D+((e₁)^*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (((π₁ ≫ π₂)^*[ModuleCat.{u + 1} Λ]).obj F)) :=
    (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) (a₁ ≫ a₂) e).inv.app K ≫
    eqToHom (by rw [Category.assoc, wa₂, ← Category.assoc, wa₁, Category.assoc]) ≫
    (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e₁ (π₁ ≫ π₂)).hom.app K ≫
    D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
      ((((π₁ ≫ π₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
  let v := D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
    ((DerivedCategory.Plus.singleFunctor _ 0).map
      ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) π₁ π₂ (π₁ ≫ π₂) rfl).inv.app F))
  let d :=
    (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₁ a₂).inv.app
    (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K)
  have hc := Etale.baseChangePullbackComparison_comp Λ e π₂ a₂ e₂ wa₂ π₁ a₁ e₁ wa₁ F
  change D+((a₁)^*[ModuleCat.{u + 1} Λ]).map c₂ ≫ c₁ ≫ v = d ≫ c₀ at hc
  have ht := Etale.lowerStarPlusTransition_comp_target Λ h a₂ h₂ wh₂ a₁ h₁ wh₁
    (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K)
  have hn := lower_transition_naturality Λ a₁ h₂ h₁ wh₁ c₂
  have hd := transition_with_coefficients_comp
    D+((a₁)^*[ModuleCat.{u + 1} Λ]) R+((h₂)_*[ModuleCat.{u + 1} Λ])
    R+((h₁)_*[ModuleCat.{u + 1} Λ])
    (Etale.lowerStarPlusTransition Λ a₂ h h₂ wh₂ _)
    (Etale.lowerStarPlusTransition Λ a₁ h₂ h₁ wh₁ _)
    (Etale.lowerStarPlusTransition Λ a₁ h₂ h₁ wh₁ _)
    (Etale.lowerStarPlusTransition Λ (a₁ ≫ a₂) h h₁
      (by rw [Category.assoc, wh₂, wh₁]) _)
    c₂ c₁ v d c₀ hn ht hc
  rw [target_transition_eq Λ e h q π₂ a₂ e₂ h₂ wa₂ wh₂ F,
    target_transition_eq Λ e₂ h₂ q π₁ a₁ e₁ h₁ wa₁ wh₁,
    target_transition_eq Λ e h q (π₁ ≫ π₂) (a₁ ≫ a₂) e₁ h₁]
  exact map_comp_with_coefficient (DerivedCategory.Plus.singleFunctor _ 0)
    D+((e₁)^*[ModuleCat.{u + 1} Λ]) R+((h₁)_*[ModuleCat.{u + 1} Λ])
    (DerivedCategory.Plus.homologyFunctor _ q) _ _
    ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) π₁ π₂ (π₁ ≫ π₂) rfl).inv.app F)
    _ hd

end AlgebraicGeometry
