/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Sites.Limits

/-! The topology and coefficient sheaf used for a product-site realization.

Source: Stacks Project, Sites, Tags 00Z4, 00Z8 and 00XA; explicit product-site
construction (blueprint: lem-weil-pbc-diagram-site-topology).
-/

@[expose] public section

universe u v uJ vJ uC vC

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The vertical-slice topology on the product category. -/
def verticalDiagramSiteTopology (J : Type uJ) (C : Type uC) [Category.{vJ} J] [Category.{vC} C]
    (K : GrothendieckTopology C) : GrothendieckTopology (J × C) where
  sieves X := {S | S.functorPullback (Prod.sectR X.1 C) ∈ K X.2}
  top_mem' X := by
    change (⊤ : Sieve X.2) ∈ K X.2
    exact K.top_mem _
  pullback_stable' {X Y} {S} f hS := by
    apply K.superset_covering _ (K.pullback_stable f.2 hS)
    intro Z g hg
    change S (Prod.mkHom (𝟙 Y.1) g ≫ f)
    change S (Prod.mkHom (𝟙 X.1) (g ≫ f.2)) at hg
    simpa using S.downward_closed hg (Prod.mkHom f.1 (𝟙 Z))
  transitive' {X} {S} hS R hR := by
    apply K.transitive hS
    intro Y f hf
    have H := hR (show S ((Prod.sectR X.1 C).map f) from hf)
    change (R.pullback ((Prod.sectR X.1 C).map f)).functorPullback
      (Prod.sectR X.1 C) ∈ K Y at H
    rwa [Sieve.functorPullback_pullback] at H

set_option backward.isDefEq.respectTransparency false in
private theorem verticalDiagramSite_isSheaf_types_iff
    (J : Type uJ) (C : Type uC) [Category.{vJ} J] [Category.{vC} C]
    (K : GrothendieckTopology C) (P : (J × C)ᵒᵖ ⥤ Type u) :
    Presieve.IsSheaf (verticalDiagramSiteTopology J C K) P ↔
      ∀ j : J, Presieve.IsSheaf K ((Prod.sectR j C).op ⋙ P) := by
  constructor
  · intro hP j U S hS x hx
    let R : Sieve (j, U) := S.functorPullback (X := (j, U)) (Prod.snd J C)
    have hR : R ∈ verticalDiagramSiteTopology J C K (j, U) := by
      change S ∈ K U
      exact hS
    let y : Presieve.FamilyOfElements P R.arrows := fun Y f hf ↦
      P.map (Prod.mkHom f.1 (𝟙 Y.2)).op (x f.2 hf)
    have hy : y.Compatible := by
      apply (Presieve.compatible_iff_sieveCompatible y).2
      rintro ⟨y₀, V₁⟩ ⟨z, W⟩ f g hf
      have H := hx.to_sieveCompatible f.2 g.2 hf
      dsimp only [y, Prod.sectR, Functor.comp_map, Functor.op_map] at H ⊢
      simp only [prod_comp_fst, prod_comp_snd]
      change P.map (Prod.mkHom (g.1 ≫ f.1) (𝟙 W)).op (x (g.2 ≫ f.2) _) = _
      rw [H]
      change (P.map (Prod.mkHom (𝟙 j) g.2).op ≫
        P.map (Prod.mkHom (g.1 ≫ f.1) (𝟙 W)).op) (x f.2 hf) =
        (P.map (Prod.mkHom f.1 (𝟙 V₁)).op ≫ P.map g.op) (x f.2 hf)
      rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp]
      congr 2
      ext; simp
    obtain ⟨t, ht, hut⟩ := hP R hR y hy
    refine ⟨t, ?_, ?_⟩
    · intro V f hf
      have H := ht ((Prod.sectR j C).map f) hf
      simpa [y, Prod.sectR, ← prod_id] using H
    · intro t' ht'
      change P.obj (op (j, U)) at t'
      apply hut t'
      rintro ⟨k, V₁⟩ f hf
      dsimp only [y]
      have H := ht' f.2 hf
      dsimp only [Prod.sectR, Functor.comp_map, Functor.op_map] at H
      rw [← H]
      change P.map f.op t' = (P.map (Prod.mkHom (𝟙 j) f.2).op ≫
        P.map (Prod.mkHom f.1 (𝟙 V₁)).op) t'
      rw [← P.map_comp, ← op_comp]
      congr 2
      ext; simp
  · rintro hP ⟨j, U⟩ R hR x hx
    let V := Prod.sectR j C
    have hV := hP j (R.functorPullback V) hR
    obtain ⟨t, ht, hut⟩ := hV (x.functorPullback V) (hx.functorPullback V)
    refine ⟨t, ?_, ?_⟩
    · rintro ⟨k, V₀⟩ f hf
      apply ((hP k).isSeparated (Sieve.pullback f.2 (R.functorPullback V))
        (K.pullback_stable f.2 hR)).ext
      intro Z g hg
      change P.map (Prod.mkHom (𝟙 k) g).op (P.map f.op t) =
        P.map (Prod.mkHom (𝟙 k) g).op (x f hf)
      have H := hx (Prod.mkHom f.1 (𝟙 Z)) (Prod.mkHom (𝟙 k) g) hg hf
        (by ext <;> simp [V])
      have ht₀ := ht (g ≫ f.2) hg
      change P.map (V.map (g ≫ f.2)).op t = x (V.map (g ≫ f.2)) hg at ht₀
      rw [← H, ← ht₀]
      dsimp only [Prod.sectR, V]
      simp only [← Functor.map_comp_apply, ← op_comp]
      congr 1
      simp
    · intro t' ht'
      apply hut t'
      intro Y f hf
      exact ht' (V.map f) hf

/-- The sheaf condition for the vertical topology is componentwise. -/
theorem verticalDiagramSite_isSheaf_iff
    (J : Type uJ) (C : Type uC) [Category.{vJ} J] [Category.{vC} C]
    (K : GrothendieckTopology C) {A : Type v} [Category.{u} A]
    (P : (J × C)ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (verticalDiagramSiteTopology J C K) P ↔
      ∀ j : J, Presheaf.IsSheaf K ((Prod.sectR j C).op ⋙ P) := by
  constructor
  · intro h j E
    exact (verticalDiagramSite_isSheaf_types_iff J C K (P ⋙ coyoneda.obj (op E))).1 (h E) j
  · intro h E
    exact (verticalDiagramSite_isSheaf_types_iff J C K (P ⋙ coyoneda.obj (op E))).2
      (fun j ↦ h j E)

/-- The vertical topology with the original contravariant diagram convention. -/
def diagramSiteTopology (J C : Type u) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) : GrothendieckTopology (Jᵒᵖ × C) :=
  verticalDiagramSiteTopology Jᵒᵖ C K

/-- The sheaf condition for the vertical topology is componentwise. -/
theorem diagramSite_isSheaf_iff
    (J C : Type u) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) {A : Type v} [Category.{u} A]
    (P : (Jᵒᵖ × C)ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (diagramSiteTopology J C K) P ↔
      ∀ j : Jᵒᵖ, Presheaf.IsSheaf K ((Prod.sectR j C).op ⋙ P) :=
  verticalDiagramSite_isSheaf_iff Jᵒᵖ C K P

/-- The coefficient sheaf, constructed by pulling back the coefficient presheaf. -/
def diagramSiteRing (J C : Type u) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{u}) :
    Sheaf (diagramSiteTopology J C K) RingCat.{u} where
  obj := (Prod.snd Jᵒᵖ C).op ⋙ O.obj
  property := by
    apply (diagramSite_isSheaf_iff J C K _).2
    intro j
    exact O.property

end CategoryTheory
