import Langlands.GroupScheme.AlgebraicallyClosedComponentBaseChangeStatement
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected

/-! # Invariance of actual components under algebraically closed field extension -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.IdentityComponent

/-- The actual pullback projection reflects equality of connected components. -/
theorem componentProjection_injective_of_isAlgClosed
    {k L : Type u} [Field k] [Field L] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k))) (φ : k →+* L) :
    Function.Injective
      (pullback.fst H.X.hom (specMap φ)).continuous.connectedComponentsMap := by
  let : GeometricallyIrreducible (specMap φ) :=
    GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed (specMap φ)
  let : GeometricallyConnected (specMap φ) :=
    GeometricallyIrreducible.geometricallyConnected (specMap φ)
  exact ((pullback.fst H.X.hom (specMap φ)).connectedComponentsHomeomorph
    (pullback.fst H.X.hom (specMap φ)).isOpenMap).injective

/-- The published extension homomorphism is bijective on all actual components. -/
theorem algebraicallyClosedComponentBaseChange :
    AlgebraicallyClosedComponentBaseChangeStatement.{u} := by
  intro k L _ _ _ _ H _ _ φ
  refine ⟨allComponentBaseChange_injective H φ, ?_⟩
  intro c
  refine ⟨(pullback.fst H.X.hom (specMap φ)).continuous.connectedComponentsMap c, ?_⟩
  apply componentProjection_injective_of_isAlgClosed H φ
  exact allComponentBaseChange_fst H φ _

end Langlands.GroupScheme.IdentityComponent
