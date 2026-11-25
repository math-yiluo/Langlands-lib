/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.EqToHom
import Mathlib.Tactic.CategoryTheory.Reassoc

/-! Generic contravariant pullback section calculation. -/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.RationalP1
section Generic

universe b hb d hd
variable {B : Type b} [Category.{hb} B] (D : B → Type d) [∀ X, Category.{hd} (D X)]
    (P : ∀ {X Y : B}, (X ⟶ Y) → D Y ⥤ D X)
    (C : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    (I : ∀ X, P (𝟙 X) ≅ 𝟭 (D X))

/-- The canonical section comparison in a contravariant functor system. -/
def canonicalSection {X W : B} (s : X ⟶ W) (f : W ⟶ X) (h : s ≫ f = 𝟙 X) :
    P f ⋙ P s ≅ 𝟭 (D X) :=
  (C s f).symm ≪≫ eqToIso (congrArg (fun t : X ⟶ X ↦ P t) h) ≪≫ I X

variable
    (hassoc : ∀ {X W V Y : B} (s : X ⟶ W) (f : W ⟶ V) (q : V ⟶ Y) (K : D Y),
      (C (s ≫ f) q).hom.app K ≫ (C s f).hom.app ((P q).obj K) =
        eqToHom (by rw [Category.assoc]) ≫ (C s (f ≫ q)).hom.app K ≫
          (P s).map ((C f q).hom.app K))
    (hunit : ∀ {X Y : B} (q : X ⟶ Y) (K : D Y),
      (C (𝟙 X) q).hom.app K ≫ (I X).hom.app ((P q).obj K) =
        eqToHom (by rw [Category.id_comp]; rfl))

include hunit in
/-- Equality transport reduces a trivial first arrow to the left unit law. -/
private theorem generic_unit {X Y : B} (a : X ⟶ X) (ha : a = 𝟙 X)
    (q : X ⟶ Y) (K : D Y) :
    (C a q).hom.app K ≫
      (eqToIso (congrArg (fun t : X ⟶ X ↦ P t) ha)).hom.app ((P q).obj K) ≫
      (I X).hom.app ((P q).obj K) = eqToHom (by rw [ha, Category.id_comp]; rfl) := by
  subst a
  dsimp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  exact (congrArg (fun t ↦ (C (𝟙 X) q).hom.app K ≫ t)
    (Category.id_comp ((I X).hom.app ((P q).obj K)))).trans (hunit q K)

include hassoc hunit in
/-- Associativity followed by the section comparison contracts a two-step path. -/
private theorem generic_normalize {X W Y : B} (s : X ⟶ W) (f : W ⟶ X)
    (q : X ⟶ Y) (h : s ≫ f = 𝟙 X) (K : D Y) :
    (C s (f ≫ q)).hom.app K ≫ (P s).map ((C f q).hom.app K) ≫
      (canonicalSection D P C I s f h).hom.app ((P q).obj K) =
        eqToHom (by rw [← Category.assoc, h, Category.id_comp]; rfl) := by
  rw [← cancel_epi (eqToHom (show (P ((s ≫ f) ≫ q)).obj K =
    (P (s ≫ f ≫ q)).obj K by rw [Category.assoc]))]
  dsimp only [canonicalSection, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← reassoc_of% (hassoc s f q K)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [generic_unit D P C I hunit (s ≫ f) h q K]
  simp only [eqToHom_trans]

include hassoc hunit in
/-- The section-normalized path is the inverse total-path compositor. -/
private theorem generic_transport {X W Y : B} (s : X ⟶ W) (f : W ⟶ X)
    (q : X ⟶ Y) (h : s ≫ f = 𝟙 X) (K : D Y) :
    (P s).map ((C f q).hom.app K) ≫
      (canonicalSection D P C I s f h).hom.app ((P q).obj K) =
        (C s (f ≫ q)).inv.app K ≫
          eqToHom (by rw [← Category.assoc, h, Category.id_comp]; rfl) := by
  exact ((C s (f ≫ q)).app K).eq_inv_comp.mpr
    (generic_normalize D P C I hassoc hunit s f q h K)

/-- Inverse total-path compositors respect an equality of base arrows. -/
private theorem generic_eq {X W Y : B} (s : X ⟶ W) (q : X ⟶ Y)
    {a b : W ⟶ Y} (e : a = b) (ha : s ≫ a = q) (hb : s ≫ b = q) (K : D Y) :
    (P s).map (eqToHom (congrArg (fun t : W ⟶ Y ↦ (P t).obj K) e)) ≫
      (C s b).inv.app K ≫
        eqToHom (congrArg (fun t : X ⟶ Y ↦ (P t).obj K) hb) =
      (C s a).inv.app K ≫
        eqToHom (congrArg (fun t : X ⟶ Y ↦ (P t).obj K) ha) := by
  subst b
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]

include hassoc hunit in
/-- A commutative square with a common section restricts to the two section comparisons. -/
private theorem generic_square {X W Y : B} (s : X ⟶ W) (f₁ f₂ : W ⟶ X)
    (q : X ⟶ Y) (h₁ : s ≫ f₁ = 𝟙 X) (h₂ : s ≫ f₂ = 𝟙 X)
    (e : f₂ ≫ q = f₁ ≫ q) (K : D Y) :
    (P s).map ((C f₂ q).inv.app K ≫
      eqToHom (congrArg (fun t : W ⟶ Y ↦ (P t).obj K) e) ≫ (C f₁ q).hom.app K) =
      (canonicalSection D P C I s f₂ h₂).hom.app ((P q).obj K) ≫
        (canonicalSection D P C I s f₁ h₁).inv.app ((P q).obj K) := by
  apply ((canonicalSection D P C I s f₁ h₁).app ((P q).obj K)).eq_comp_inv.mpr
  rw [← cancel_epi ((P s).map ((C f₂ q).hom.app K))]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, Iso.app_hom]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [generic_transport D P C I hassoc hunit, generic_transport D P C I hassoc hunit]
  exact generic_eq D P C s q e
    (by rw [← Category.assoc, h₂, Category.id_comp])
    (by rw [← Category.assoc, h₁, Category.id_comp]) K

include hassoc hunit in
/-- The section calculation through specified ambient and section comparisons. -/
theorem contravariantPullSectionSquare {X W Y : B} (s : X ⟶ W) (f₁ f₂ : W ⟶ X)
    (q : X ⟶ Y) (h₁ : s ≫ f₁ = 𝟙 X) (h₂ : s ≫ f₂ = 𝟙 X)
    (e : f₂ ≫ q = f₁ ≫ q)
    (b : P q ⋙ P f₂ ≅ P q ⋙ P f₁)
    (s₁ : P f₁ ⋙ P s ≅ 𝟭 (D X)) (s₂ : P f₂ ⋙ P s ≅ 𝟭 (D X))
    (hb : b = (C f₂ q).symm ≪≫
      eqToIso (congrArg (fun t : W ⟶ Y ↦ P t) e) ≪≫ C f₁ q)
    (hs₁ : s₁ = canonicalSection D P C I s f₁ h₁)
    (hs₂ : s₂ = canonicalSection D P C I s f₂ h₂) (K : D Y) :
    (P s).map ((b.symm.app K).inv) =
      s₂.hom.app ((P q).obj K) ≫ s₁.inv.app ((P q).obj K) := by
  subst b s₁ s₂
  simpa only [Iso.symm_inv, Iso.app_inv, Iso.app_hom, Iso.trans_hom,
    NatTrans.comp_app, Iso.symm_hom, eqToIso.hom, eqToHom_app] using
    generic_square D P C I hassoc hunit s f₁ f₂ q h₁ h₂ e K

end Generic
end AlgebraicGeometry.ProEtale.RationalP1
