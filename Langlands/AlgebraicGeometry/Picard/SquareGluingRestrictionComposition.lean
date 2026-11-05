import Langlands.AlgebraicGeometry.Picard.SquareGluingRestrictionComparison

/-! # Composition of restriction of actual Picard square gluing data -/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SquareGluingRestrictionComposition

section Face

open Langlands.Scheme.Modules.UnitCocycleDescentUniqueness
open Langlands.SchemeModule.RigidifiedModule

private lemma compIso_assoc {X Y Z W : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : Z ⟶ W) (ab : X ⟶ Z) (bc : Y ⟶ W) (abc : X ⟶ W)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc) (habc : ab ≫ c = abc)
    (habc' : a ≫ bc = abc) (M : W.Modules) :
    (compIso a b ab hab ((Scheme.Modules.pullback c).obj M)).hom ≫
        (compIso ab c abc habc M).hom =
      (Scheme.Modules.pullback a).map (compIso b c bc hbc M).hom ≫
        (compIso a bc abc habc' M).hom :=
  compHom_assoc a b c ab bc abc hab hbc habc habc' M

variable {Y₀ Y₁ T₀ T₁ S₀ S₁ : Scheme.{u}}
  (i : Y₀ ⟶ Y₁) (ι : T₀ ⟶ T₁) (κ : S₀ ⟶ S₁)
  (g₁ : T₁ ⟶ Y₁) (g₀ : T₀ ⟶ Y₀)
  (h₁ : S₁ ⟶ T₁) (h₀ : S₀ ⟶ T₀)
  (k : ι ≫ g₁ = g₀ ≫ i) (l : κ ≫ h₁ = h₀ ≫ ι)
  (m : κ ≫ (h₁ ≫ g₁) = (h₀ ≫ g₀) ≫ i)

private lemma compIso_rfl {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (M : Z.Modules) : compIso a b (a ≫ b) rfl M =
      (Scheme.Modules.pullbackComp a b).app M := by
  apply Iso.ext
  simp only [compIso_hom, compHom_rfl, Iso.app_hom]

private lemma module_square_paste (M : Y₁.Modules) :
    (Scheme.Modules.pullback κ).map
        ((Scheme.Modules.pullbackComp h₁ g₁).hom.app M) ≫
      (Langlands.Scheme.Modules.squarePullbackIso i κ (h₀ ≫ g₀) (h₁ ≫ g₁) m M).hom =
    (Langlands.Scheme.Modules.squarePullbackIso ι κ h₀ h₁ l
        ((Scheme.Modules.pullback g₁).obj M)).hom ≫
      (Scheme.Modules.pullback h₀).map
        (Langlands.Scheme.Modules.squarePullbackIso i ι g₀ g₁ k M).hom ≫
      (Scheme.Modules.pullbackComp h₀ g₀).hom.app
        ((Scheme.Modules.pullback i).obj M) := by
  let z := (h₀ ≫ g₀) ≫ i
  have ha : (h₀ ≫ ι) ≫ g₁ = z := by
    dsimp [z]
    rw [Category.assoc, k, ← Category.assoc]
  have hb : h₀ ≫ (g₀ ≫ i) = z := (Category.assoc _ _ _).symm
  have e₁ := compIso_assoc κ h₁ g₁ (h₀ ≫ ι) (h₁ ≫ g₁) z l rfl ha m M
  have e₂ := compIso_assoc h₀ ι g₁ (h₀ ≫ ι) (g₀ ≫ i) z rfl k ha hb M
  have e₃ := compIso_assoc h₀ g₀ i (h₀ ≫ g₀) (g₀ ≫ i) z rfl rfl rfl hb M
  rw [← cancel_mono (compIso (h₀ ≫ g₀) i z rfl M).hom]
  rw [squarePullbackIso_hom_eq_compIso i κ (h₀ ≫ g₀) (h₁ ≫ g₁) m
      z m rfl,
    squarePullbackIso_hom_eq_compIso ι κ h₀ h₁ l (h₀ ≫ ι) l rfl,
    squarePullbackIso_hom_eq_compIso i ι g₀ g₁ k (g₀ ≫ i) k rfl]
  simp only [← Iso.app_hom, ← compIso_rfl, Functor.map_comp, Category.assoc]
  rw [e₃]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← e₂]
  simp only [Iso.inv_hom_id_assoc]
  exact e₁.symm

private lemma pullbackComp_app (L : PicardGroupoid Y₁) :
    ((PicardGroupoid.pullbackComp h₁ g₁).hom.app L).iso.hom.hom =
      (Scheme.Modules.pullbackComp h₁ g₁).hom.app L.of.obj := rfl

/-- The ordinary Picard comparisons respect two pasted commuting faces. -/
lemma square_paste (L : PicardGroupoid Y₁) :
    (PicardGroupoid.pullback κ).map
        ((PicardGroupoid.pullbackComp h₁ g₁).hom.app L) ≫
      (PicardGroupoid.squarePullbackIso κ (h₀ ≫ g₀) (h₁ ≫ g₁) i m).hom.app L =
    (PicardGroupoid.squarePullbackIso κ h₀ h₁ ι l).hom.app
        ((PicardGroupoid.pullback g₁).obj L) ≫
      (PicardGroupoid.pullback h₀).map
        ((PicardGroupoid.squarePullbackIso ι g₀ g₁ i k).hom.app L) ≫
      (PicardGroupoid.pullbackComp h₀ g₀).hom.app
        ((PicardGroupoid.pullback i).obj L) := by
  apply Core.hom_ext
  apply ObjectProperty.hom_ext
  change
    (Scheme.Modules.pullback κ).map
        (((PicardGroupoid.pullbackComp h₁ g₁).hom.app L).iso.hom.hom) ≫
      ((PicardGroupoid.squarePullbackIso κ (h₀ ≫ g₀) (h₁ ≫ g₁) i m).hom.app
        L).iso.hom.hom =
    ((PicardGroupoid.squarePullbackIso κ h₀ h₁ ι l).hom.app
        ((PicardGroupoid.pullback g₁).obj L)).iso.hom.hom ≫
      (Scheme.Modules.pullback h₀).map
        (((PicardGroupoid.squarePullbackIso ι g₀ g₁ i k).hom.app L).iso.hom.hom) ≫
      ((PicardGroupoid.pullbackComp h₀ g₀).hom.app
        ((PicardGroupoid.pullback i).obj L)).iso.hom.hom
  simp only [pullbackComp_app, SquareTrivialEffectivity.squarePullbackIso_app]
  simpa only [PicardGroupoid.pullback, LineBundle.pullback, Functor.core,
    Core.functorToCore, Core.inclusion, ObjectProperty.lift, LineBundle.forget,
    ObjectProperty.ι, Functor.comp_obj, inducedFunctor] using
    module_square_paste i ι κ g₁ g₀ h₁ h₀ k l m L.of.obj

end Face

section Composition

variable {Y₀ Y₁ Y₂ T₀ T₁ T₂ S₀ S₁ S₂ : Scheme.{u}}
  (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂)
  (ι₁ : T₀ ⟶ T₁) (ι₂ : T₀ ⟶ T₂)
  (κ₁ : S₀ ⟶ S₁) (κ₂ : S₀ ⟶ S₂)
  (g₁ : T₁ ⟶ Y₁) (g₂ : T₂ ⟶ Y₂) (g₀ : T₀ ⟶ Y₀)
  (h₁ : S₁ ⟶ T₁) (h₂ : S₂ ⟶ T₂) (h₀ : S₀ ⟶ T₀)
  (k₁ : ι₁ ≫ g₁ = g₀ ≫ i₁) (k₂ : ι₂ ≫ g₂ = g₀ ≫ i₂)
  (l₁ : κ₁ ≫ h₁ = h₀ ≫ ι₁) (l₂ : κ₂ ≫ h₂ = h₀ ≫ ι₂)
  (m₁ : κ₁ ≫ (h₁ ≫ g₁) = (h₀ ≫ g₀) ≫ i₁)
  (m₂ : κ₂ ≫ (h₂ ≫ g₂) = (h₀ ≫ g₀) ≫ i₂)

/-- Successive restrictions of actual square gluing data agree naturally with
restriction along the composite maps, through the ordinary pullback comparisons. -/
def pullbackComp :
    SquareGluingRestriction.pullback i₁ i₂ ι₁ ι₂ g₁ g₂ g₀ k₁ k₂ ⋙
        SquareGluingRestriction.pullback ι₁ ι₂ κ₁ κ₂ h₁ h₂ h₀ l₁ l₂ ≅
      SquareGluingRestriction.pullback i₁ i₂ κ₁ κ₂
        (h₁ ≫ g₁) (h₂ ≫ g₂) (h₀ ≫ g₀) m₁ m₂ :=
  NatIso.ofComponents
    (fun D ↦ Comma.isoMk
      ((PicardGroupoid.pullbackComp h₁ g₁).app D.left)
      ((PicardGroupoid.pullbackComp h₂ g₂).app D.right) (by
        change (PicardGroupoid.pullback κ₁).map
            ((PicardGroupoid.pullbackComp h₁ g₁).hom.app D.left) ≫
          ((PicardGroupoid.squarePullbackIso κ₁ (h₀ ≫ g₀) (h₁ ≫ g₁) i₁ m₁).hom.app
              D.left ≫
            (PicardGroupoid.pullback (h₀ ≫ g₀)).map D.hom ≫
            (PicardGroupoid.squarePullbackIso κ₂ (h₀ ≫ g₀) (h₂ ≫ g₂) i₂ m₂).inv.app
              D.right) =
          ((PicardGroupoid.squarePullbackIso κ₁ h₀ h₁ ι₁ l₁).hom.app
              ((PicardGroupoid.pullback g₁).obj D.left) ≫
            (PicardGroupoid.pullback h₀).map
              ((PicardGroupoid.squarePullbackIso ι₁ g₀ g₁ i₁ k₁).hom.app D.left ≫
                (PicardGroupoid.pullback g₀).map D.hom ≫
                (PicardGroupoid.squarePullbackIso ι₂ g₀ g₂ i₂ k₂).inv.app D.right) ≫
            (PicardGroupoid.squarePullbackIso κ₂ h₀ h₂ ι₂ l₂).inv.app
              ((PicardGroupoid.pullback g₂).obj D.right)) ≫
            (PicardGroupoid.pullback κ₂).map
              ((PicardGroupoid.pullbackComp h₂ g₂).hom.app D.right)
        rw [← cancel_mono
          ((PicardGroupoid.squarePullbackIso κ₂ (h₀ ≫ g₀) (h₂ ≫ g₂) i₂ m₂).hom.app
            D.right)]
        simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app,
          Category.comp_id]
        rw [square_paste i₂ ι₂ κ₂ g₂ g₀ h₂ h₀ k₂ l₂ m₂ D.right]
        simp only [Functor.comp_obj, Functor.map_comp, Category.assoc,
          ← Iso.app_hom, ← Iso.app_inv, Iso.inv_hom_id_assoc,
          Iso.map_inv_hom_id_assoc]
        simp only [Iso.app_hom]
        rw [reassoc_of% square_paste i₁ ι₁ κ₁ g₁ g₀ h₁ h₀ k₁ l₁ m₁ D.left]
        have n := (PicardGroupoid.pullbackComp h₀ g₀).hom.naturality D.hom
        rw [← n]
        rfl))
    (fun f ↦ by
      apply Comma.hom_ext
      · exact (PicardGroupoid.pullbackComp h₁ g₁).hom.naturality f.left
      · exact (PicardGroupoid.pullbackComp h₂ g₂).hom.naturality f.right)

end Composition

end Langlands.AlgebraicGeometry.Picard.SquareGluingRestrictionComposition
