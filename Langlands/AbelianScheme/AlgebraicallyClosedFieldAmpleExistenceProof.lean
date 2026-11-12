import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceStatement
import Langlands.AbelianScheme.AlgebraicallyClosedProjectivityProof
import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOneAmpleProof
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof

/-! # Ample existence over an algebraically closed field

Pull the actual ample degree-one twisting bundle back along the closed immersion
provided by projectivity of the group scheme.
-/

universe u

namespace Langlands.GroupScheme

/-- Every commutative smooth proper geometrically connected group scheme over
an algebraically closed field admits an actual ample line bundle. -/
theorem algebraicallyClosedFieldAmpleExistence :
    AlgebraicallyClosedFieldAmpleExistenceStatement.{u} := by
  intro K _ _ G _ hSmooth hProper hConnected
  obtain ⟨n, i, hi, _⟩ :=
    algebraicallyClosedProjectivity K G hSmooth hProper hConnected
  obtain ⟨L, _, hL⟩ :=
    Langlands.AlgebraicGeometry.projectiveSpaceTwistOneAmple K n
  refine ⟨(Langlands.AlgebraicGeometry.Picard.LineBundle.pullback i).obj L, ?_⟩
  exact Langlands.AlgebraicGeometry.Picard.closedImmersionPullbackAmple
    (Langlands.AlgebraicGeometry.ProjectiveSpace K n) G.X.left i L hi hL

end Langlands.GroupScheme
