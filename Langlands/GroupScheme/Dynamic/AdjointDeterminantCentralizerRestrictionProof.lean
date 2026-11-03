import Langlands.GroupScheme.Dynamic.AdjointDeterminantCentralizerRestrictionStatement
import Langlands.GroupScheme.Dynamic.AdjointDeterminantFunctorialityProof

/-! # Levi restriction of the actual parabolic adjoint determinant -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

/-- Restricting parabolic conjugation to the centralizer gives centralizer conjugation. -/
theorem parabolicAdjointAction_restrict_centralizer {S : Scheme.{u}}
    {G P Z U : GroupScheme S} {χ : (Gm S).toGrp ⟶ G}
    {iP : P ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
    (hP : (parabolic χ).IsRepresentedBy iP)
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy iU) :
    (parabolicAdjointAction hP hU).restrict (centralizerToParabolic hP hZ) =
      centralizerAdjointAction hZ hU := by
  apply eq_centralizerAdjointAction hZ hU
  intro T m u
  rw [AutomorphicAction.restrict_act, parabolicAdjointAction_act_comp]
  have hj := congrArg (fun f : Z ⟶ G => f.hom.hom)
    (centralizerToParabolic_comp hP hZ)
  change (centralizerToParabolic hP hZ).hom.hom ≫ iP.hom.hom = iZ.hom.hom at hj
  simp only [Category.assoc, hj]

/-- The exact published arbitrary-ring Levi restriction statement. -/
theorem adjointDeterminantCentralizerRestriction :
    AdjointDeterminantCentralizerRestrictionStatement.{u} := by
  intro R G χ P Z U iP iZ iU hP hZ hU _ _ _ d c
  change characterRestrict (centralizerToParabolic hP hZ)
      ((parabolicAdjointAction hP hU).determinantCharacter c) = _
  rw [AutomorphicAction.determinantCharacter_restrict,
    parabolicAdjointAction_restrict_centralizer hP hZ hU]

end Langlands.GroupScheme.Dynamic
