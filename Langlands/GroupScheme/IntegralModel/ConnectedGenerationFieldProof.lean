import Langlands.GroupScheme.IntegralModel.ConnectedGenerationFieldGeneration
import Langlands.GroupScheme.IntegralModel.ConnectedGenerationFiniteIndexProof

/-! # The field step of KP Lemma A.4.26 -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Finite-index images of a finite family of smooth affine geometrically
connected groups generate exactly the rational points of the identity component. -/
theorem connectedGenerationField : ConnectedGenerationFieldStatement.{u} := by
  intro k _ _ G _ hG n Y _ hY hconn f hfinite N i hi
  let : Smooth G.X.hom := hG
  let : ∀ j, Smooth (Y j).X.hom := hY
  let : ∀ j, GeometricallyConnected (Y j).X.hom := hconn
  have hA : ∀ j, Smooth (Y j).X.hom ∧ IsAffineHom (Y j).X.hom ∧
      ConnectedSpace (Y j).X.left := by
    intro j
    exact ⟨hY j, inferInstance,
      GeometricallyConnected.connectedSpace_of_subsingleton (f := (Y j).X.hom)⟩
  obtain ⟨H, j, _, _, _, hj, hjRange⟩ :=
    ConnectedGenerationField.exists_generated_points f hA
  have hfinite' : (rationalPoints.map j).range.FiniteIndex := by
    rwa [hjRange]
  apply le_antisymm (ConnectedGeneration.generatedImages_le_componentRange f i hi)
  rw [← hjRange]
  exact ConnectedGeneration.componentRange_le_of_finiteIndex j hj hfinite' N i hi

end Langlands.GroupScheme
