import Langlands.GroupScheme.Adjoint.BaseChangeStatement
import Langlands.GroupScheme.Adjoint.GeometricBaseChange
import Langlands.GroupScheme.Adjoint.QuotientDescent
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Reductive.FiniteCenterBaseChange

/-! # Field base change of actual adjoint quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Arbitrary field extension preserves the full actual adjoint-quotient interface. -/
theorem adjointQuotientBaseChangeStatement :
    AdjointQuotientBaseChangeStatement.{u} := by
  intro k K _ _ _ G A q hq
  let b := algebraBaseMap k K
  let : Flat ((GroupScheme.baseChange b).map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b q.hom.hom hq.flat
  let : Surjective ((GroupScheme.baseChange b).map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom hq.surjective
  let : LocallyOfFinitePresentation ((GroupScheme.baseChange b).map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) b q.hom.hom
      hq.locallyOfFinitePresentation
  have hG : IsConnectedReductive ((GroupScheme.baseChange b).obj G) :=
    connectedReductiveFieldExtensionStatement k K G hq.isConnectedReductive
  have hA : IsAdjoint ((GroupScheme.baseChange b).obj A) :=
    ⟨⟨connectedReductiveFieldExtensionStatement k K A
      hq.isAdjoint.isSemisimple.isConnectedReductive,
      hq.isAdjoint.isSemisimple.hasFiniteCenter.baseChange b⟩,
      center_eq_bot_baseChange b hq.isAdjoint.center_eq_bot⟩
  exact IsAdjointQuotient.of_fppf hG hA (kernelCenter_baseChange b hq.kernelCenter)

end Langlands.GroupScheme
