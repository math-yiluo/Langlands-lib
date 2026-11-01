import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Open immersions into unramified morphisms -/

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace Langlands.AlgebraicGeometry

theorem isOpenImmersion_of_comp_of_unramified {Y X S : Scheme.{u}}
    (g : Y ⟶ X) (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] [IsOpenImmersion (g ≫ f)] :
    IsOpenImmersion g := by
  let gr : Y ⟶ pullback (g ≫ f) f := pullback.lift (𝟙 Y) g (by simp)
  have : IsOpenImmersion gr :=
    MorphismProperty.of_isPullback (pullback_lift_diagonal_isPullback g f)
      (inferInstanceAs (IsOpenImmersion (pullback.diagonal f)))
  have hg : g = gr ≫ pullback.snd _ _ := by
    dsimp [gr]
    rw [pullback.lift_snd]
  rw [hg]
  infer_instance

end Langlands.AlgebraicGeometry
