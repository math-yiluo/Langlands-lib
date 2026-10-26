import Langlands.Cohomology.AcyclicResolution.Lift
import Langlands.Cohomology.AcyclicResolution.Statement

/-!
# Lifting right resolutions into injective resolutions

This module proves `ResolutionLiftStatement`: a right resolution `ε : A[0] ⟶ K` of an
object `A` of an abelian category maps to any injective resolution `I` of `A` by a cochain
map compatible with the augmentations, and any two such maps are homotopic.

The existence part is `AcyclicResolution.lift ε (𝟙 A) I.ι` with `AcyclicResolution.comp_lift`;
the uniqueness part is `AcyclicResolution.homotopyOfComp`.
-/

open CategoryTheory

namespace Langlands.Cohomology

universe u v

/-- A right resolution maps to any injective resolution of the same object,
and two augmentation-compatible lifts are homotopic. -/
theorem resolutionLiftStatement : ResolutionLiftStatement.{u, v} := by
  intro C _ _ A K ε _ I
  refine ⟨⟨AcyclicResolution.lift ε (𝟙 A) I.ι, ?_⟩, fun φ ψ hφ hψ =>
    ⟨AcyclicResolution.homotopyOfComp ε φ ψ (hφ.trans hψ.symm)⟩⟩
  rw [AcyclicResolution.comp_lift, CategoryTheory.Functor.map_id, Category.id_comp]

end Langlands.Cohomology
