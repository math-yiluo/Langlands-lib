import Langlands.GroupScheme.IntegralModel.SmoothIntersection
import Langlands.GroupScheme.IntegralModel.SchematicClosureProof
import Langlands.GroupScheme.IntegralModel.SmootheningProof
import Langlands.GroupScheme.HomScheme.Graph

/-! # The diagonal-closure and smoothening construction of an intersection model -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

/-- KP A.6.6 follows from the actual schematic-closure and smoothening constructions. -/
theorem smoothIntersection_of_closure_smoothening
    (hclosure : IntegralModelSchematicClosureStatement.{u})
    (hsmoothening : SmootheningStatement.{u}) :
    SmoothIntersectionStatement.{u} := by
  intro R _ _ _ _ _ K _ _ _ G _ hG M N
  have hΔ : IsClosedSubgroup (HomScheme.graphHom (𝟙 G)) :=
    HomScheme.isClosedImmersion_graphHom (𝟙 G)
  obtain ⟨C, φ, hφ⟩ :=
    hclosure R K (G ⊗ G) (M.product N) G (HomScheme.graphHom (𝟙 G)) hΔ
  let α : C.Hom M (𝟙 G) := by
    simpa only [HomScheme.graphHom_fst] using φ.comp (M.productFst N)
  let β : C.Hom N (𝟙 G) := by
    simpa only [HomScheme.graphHom_snd] using φ.comp (M.productSnd N)
  have hC : C.integralPoints = M.integralPoints ⊓ N.integralPoints := by
    rw [hφ.integralPoints_eq_comap]
    exact product_integralPoints_comap_diagonal M N
  obtain ⟨L, π, hπ⟩ := hsmoothening R K G hG C
  refine ⟨L, hπ.1, ?_, ?_, hπ.integralPoints_eq.trans hC⟩
  · exact ⟨by simpa only [Category.id_comp] using π.comp α⟩
  · exact ⟨by simpa only [Category.id_comp] using π.comp β⟩

/-- The published closure construction leaves only smoothening existence as an input. -/
theorem smoothIntersection_of_smoothening
    (hsmoothening : SmootheningStatement.{u}) :
    SmoothIntersectionStatement.{u} :=
  smoothIntersection_of_closure_smoothening integralModelSchematicClosure hsmoothening

/-- **Smooth intersection model** (KP A.6.6): the actual intersection of the integral-point
subgroups of two supplied models is realized by a smooth model of the same generic group. -/
theorem smoothIntersection : SmoothIntersectionStatement.{u} :=
  smoothIntersection_of_smoothening smoothening_exists

end Langlands.GroupScheme.IntegralModel
