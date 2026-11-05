import Langlands.AlgebraicGeometry.Picard.SquareGluingRestriction
import Langlands.AlgebraicGeometry.Picard.SquareTrivialEffectivity
import Langlands.AlgebraicGeometry.Modules.SquareLocalIsoLift

/-! # Restriction commutes with the actual Picard square comparison -/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SquareGluingRestrictionComparison

variable {Y₀ Y₁ Y₂ Y T₀ T₁ T₂ T : Scheme.{u}}
  (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y)
  (w : i₁ ≫ j₁ = i₂ ≫ j₂)
  (t : T ⟶ Y) (s₁ : T₁ ⟶ T) (s₂ : T₂ ⟶ T)
  (ι₁ : T₀ ⟶ T₁) (ι₂ : T₀ ⟶ T₂)
  (wT : ι₁ ≫ s₁ = ι₂ ≫ s₂)
  (g₁ : T₁ ⟶ Y₁) (g₂ : T₂ ⟶ Y₂) (g₀ : T₀ ⟶ Y₀)
  (h₁ : s₁ ≫ t = g₁ ≫ j₁) (h₂ : s₂ ≫ t = g₂ ≫ j₂)
  (k₁ : ι₁ ≫ g₁ = g₀ ≫ i₁) (k₂ : ι₂ ≫ g₂ = g₀ ≫ i₂)

/-- The ordinary comparisons commute around the cube on actual Picard arrows. -/
lemma cube_coherence (L : PicardGroupoid Y) :
    (PicardGroupoid.squarePullbackIso ι₁ ι₂ s₁ s₂ wT).hom.app
        ((PicardGroupoid.pullback t).obj L) ≫
      (PicardGroupoid.pullback ι₂).map
        ((PicardGroupoid.squarePullbackIso s₂ g₂ t j₂ h₂).hom.app L) ≫
      (PicardGroupoid.squarePullbackIso ι₂ g₀ g₂ i₂ k₂).hom.app
        ((PicardGroupoid.pullback j₂).obj L) =
    (PicardGroupoid.pullback ι₁).map
        ((PicardGroupoid.squarePullbackIso s₁ g₁ t j₁ h₁).hom.app L) ≫
      (PicardGroupoid.squarePullbackIso ι₁ g₀ g₁ i₁ k₁).hom.app
        ((PicardGroupoid.pullback j₁).obj L) ≫
      (PicardGroupoid.pullback g₀).map
        ((PicardGroupoid.squarePullbackIso i₁ i₂ j₁ j₂ w).hom.app L) := by
  apply Core.hom_ext
  apply ObjectProperty.hom_ext
  change
    ((PicardGroupoid.squarePullbackIso ι₁ ι₂ s₁ s₂ wT).hom.app
        ((PicardGroupoid.pullback t).obj L)).iso.hom.hom ≫
      (Scheme.Modules.pullback ι₂).map
        (((PicardGroupoid.squarePullbackIso s₂ g₂ t j₂ h₂).hom.app L).iso.hom.hom) ≫
      ((PicardGroupoid.squarePullbackIso ι₂ g₀ g₂ i₂ k₂).hom.app
        ((PicardGroupoid.pullback j₂).obj L)).iso.hom.hom =
    (Scheme.Modules.pullback ι₁).map
        (((PicardGroupoid.squarePullbackIso s₁ g₁ t j₁ h₁).hom.app L).iso.hom.hom) ≫
      ((PicardGroupoid.squarePullbackIso ι₁ g₀ g₁ i₁ k₁).hom.app
        ((PicardGroupoid.pullback j₁).obj L)).iso.hom.hom ≫
      (Scheme.Modules.pullback g₀).map
        (((PicardGroupoid.squarePullbackIso i₁ i₂ j₁ j₂ w).hom.app L).iso.hom.hom)
  simp only [SquareTrivialEffectivity.squarePullbackIso_app]
  simpa only [Langlands.Scheme.Modules.SquareLocalIsoLift.legIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc, PicardGroupoid.pullback, LineBundle.pullback,
    Functor.core, Core.functorToCore, Core.inclusion, ObjectProperty.lift,
    LineBundle.forget, ObjectProperty.ι, Functor.comp_obj, inducedFunctor] using
    Langlands.Scheme.Modules.SquareLocalIsoLift.cube_coherence
      i₁ i₂ j₁ j₂ w t s₁ s₂ ι₁ ι₂ wT g₁ g₂ g₀ h₁ h₂ k₁ k₂ L.of.obj

/-- Pulling back a total bundle then comparing is naturally isomorphic to
comparing first and restricting the actual gluing datum along the cube. -/
def comparisonIso :
    PicardGroupoid.pullback t ⋙
        PicardGroupoid.squareGluingComparison ι₁ ι₂ s₁ s₂ wT ≅
      PicardGroupoid.squareGluingComparison i₁ i₂ j₁ j₂ w ⋙
        SquareGluingRestriction.pullback i₁ i₂ ι₁ ι₂ g₁ g₂ g₀ k₁ k₂ :=
  NatIso.ofComponents
    (fun L ↦ Comma.isoMk
      ((PicardGroupoid.squarePullbackIso s₁ g₁ t j₁ h₁).app L)
      ((PicardGroupoid.squarePullbackIso s₂ g₂ t j₂ h₂).app L) (by
        change (PicardGroupoid.pullback ι₁).map
            ((PicardGroupoid.squarePullbackIso s₁ g₁ t j₁ h₁).hom.app L) ≫
          ((PicardGroupoid.squarePullbackIso ι₁ g₀ g₁ i₁ k₁).hom.app
              ((PicardGroupoid.pullback j₁).obj L) ≫
            (PicardGroupoid.pullback g₀).map
              ((PicardGroupoid.squarePullbackIso i₁ i₂ j₁ j₂ w).hom.app L) ≫
            (PicardGroupoid.squarePullbackIso ι₂ g₀ g₂ i₂ k₂).inv.app
              ((PicardGroupoid.pullback j₂).obj L)) =
          (PicardGroupoid.squarePullbackIso ι₁ ι₂ s₁ s₂ wT).hom.app
              ((PicardGroupoid.pullback t).obj L) ≫
            (PicardGroupoid.pullback ι₂).map
              ((PicardGroupoid.squarePullbackIso s₂ g₂ t j₂ h₂).hom.app L)
        rw [← cancel_mono ((PicardGroupoid.squarePullbackIso ι₂ g₀ g₂ i₂ k₂).hom.app
          ((PicardGroupoid.pullback j₂).obj L))]
        simpa only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app,
          Category.comp_id] using
          (cube_coherence i₁ i₂ j₁ j₂ w t s₁ s₂ ι₁ ι₂ wT
            g₁ g₂ g₀ h₁ h₂ k₁ k₂ L).symm))
    (fun f ↦ by
      apply Comma.hom_ext
      · exact (PicardGroupoid.squarePullbackIso s₁ g₁ t j₁ h₁).hom.naturality f
      · exact (PicardGroupoid.squarePullbackIso s₂ g₂ t j₂ h₂).hom.naturality f)

open InfinitesimalAffineOpenSquare

/-- The comparison on the exact inverse-image square agrees with restriction
of the original comparison through its ordinary pullback comparisons. -/
def toOpenIso (U : Y.Opens) :
    PicardGroupoid.pullback U.ι ⋙
        PicardGroupoid.squareGluingComparison
          (leftRestriction i₁ j₁ U) (rightRestriction i₁ i₂ j₁ j₂ w U)
          (j₁ ∣_ U) (j₂ ∣_ U) (restriction_comm i₁ i₂ j₁ j₂ w U) ≅
      PicardGroupoid.squareGluingComparison i₁ i₂ j₁ j₂ w ⋙
        SquareGluingRestriction.toOpen i₁ i₂ j₁ j₂ w U :=
  comparisonIso i₁ i₂ j₁ j₂ w U.ι (j₁ ∣_ U) (j₂ ∣_ U)
    (leftRestriction i₁ j₁ U) (rightRestriction i₁ i₂ j₁ j₂ w U)
    (restriction_comm i₁ i₂ j₁ j₂ w U)
    (j₁ ⁻¹ᵁ U).ι (j₂ ⁻¹ᵁ U).ι ((i₁ ≫ j₁) ⁻¹ᵁ U).ι
    (morphismRestrict_ι j₁ U) (morphismRestrict_ι j₂ U)
    (leftRestriction_ι i₁ j₁ U) (rightRestriction_ι i₁ i₂ j₁ j₂ w U)

end Langlands.AlgebraicGeometry.Picard.SquareGluingRestrictionComparison
