import Langlands.AlgebraicGeometry.Modules.SquareTrivialEffectivity
import Langlands.AlgebraicGeometry.Picard.InfinitesimalGluing

/-! # Actual Picard effectivity for globally trivial legs -/

universe u

open CategoryTheory AlgebraicGeometry Langlands.SchemeModule
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SquareTrivialEffectivity

variable {Y₀ Y₁ Y₂ Y : Scheme.{u}}
  (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y)
  (w : i₁ ≫ j₁ = i₂ ≫ j₂)

private lemma eqToHom_iso_hom_hom {X : Scheme.{u}} {A B : PicardGroupoid X} (e : A = B) :
    (eqToHom e).iso.hom.hom = eqToHom (congrArg (fun A : PicardGroupoid X ↦ A.of.obj) e) := by
  subst e
  rfl

/-- Forgetting the ordinary Picard square comparison gives precisely the ordinary
module square comparison. -/
lemma squarePullbackIso_app (L : PicardGroupoid Y) :
    ((PicardGroupoid.squarePullbackIso i₁ i₂ j₁ j₂ w).hom.app L).iso.hom.hom =
      (squarePullbackIso j₂ i₁ i₂ j₁ w L.of.obj).hom := by
  simp only [PicardGroupoid.squarePullbackIso, squarePullbackIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, coreCategory_comp_iso, eqToIso.hom, eqToHom_app,
    ObjectProperty.FullSubcategory.comp_hom, Iso.app_hom, Iso.app_inv,
    Scheme.Modules.pullbackCongr]
  rw [eqToHom_iso_hom_hom]
  rfl

variable (hi₂ : Function.Surjective i₂.appTop.hom)
  (hn : IsNilpotent (RingHom.ker i₂.appTop.hom))
  (D : PicardGroupoid.SquareGluingData i₁ i₂)
  (τ₁ : D.left.of.obj ≅ structureModule Y₁)
  (τ₂ : D.right.of.obj ≅ structureModule Y₂)

/-- The overlap of an actual Picard gluing datum, as an actual module isomorphism. -/
def overlapIso :
    (Scheme.Modules.pullback i₁).obj D.left.of.obj ≅
      (Scheme.Modules.pullback i₂).obj D.right.of.obj :=
  (LineBundle.forget Y₀).mapIso D.hom.iso

/-- An actual gluing datum with globally trivial legs comes from the trivial
line bundle, retaining the specified ordinary Picard comparison. -/
def trivialObjectIso :
    (PicardGroupoid.squareGluingComparison i₁ i₂ j₁ j₂ w).obj
        (Core.mk (LineBundle.trivial Y)) ≅ D := by
  let e₁ := Langlands.Scheme.Modules.SquareTrivialEffectivity.leftIso j₁ τ₁
  let e₂ := Langlands.Scheme.Modules.SquareTrivialEffectivity.rightIso
    i₁ i₂ j₁ j₂ w hi₂ hn τ₁ τ₂ (overlapIso i₁ i₂ D)
  refine Comma.isoMk (Core.isoMk (ObjectProperty.isoMk _ e₁))
    (Core.isoMk (ObjectProperty.isoMk _ e₂)) ?_
  apply Core.hom_ext
  apply ObjectProperty.hom_ext
  change (Scheme.Modules.pullback i₁).map e₁.hom ≫ D.hom.iso.hom.hom =
    ((PicardGroupoid.squarePullbackIso i₁ i₂ j₁ j₂ w).hom.app
      (Core.mk (LineBundle.trivial Y))).iso.hom.hom ≫
        (Scheme.Modules.pullback i₂).map e₂.hom
  rw [squarePullbackIso_app]
  exact (Langlands.Scheme.Modules.SquareTrivialEffectivity.compatible
    i₁ i₂ j₁ j₂ w hi₂ hn τ₁ τ₂ (overlapIso i₁ i₂ D)).symm

include hi₂ hn τ₁ τ₂ in
/-- Every datum with globally trivial legs lies in the actual comparison's
essential image when its second overlap map is nilpotent-surjective on sections. -/
lemma exists_preimage :
    ∃ L : PicardGroupoid Y,
      Nonempty ((PicardGroupoid.squareGluingComparison i₁ i₂ j₁ j₂ w).obj L ≅ D) :=
  ⟨Core.mk (LineBundle.trivial Y),
    ⟨trivialObjectIso i₁ i₂ j₁ j₂ w hi₂ hn D τ₁ τ₂⟩⟩

end Langlands.AlgebraicGeometry.Picard.SquareTrivialEffectivity
