import Langlands.GroupScheme.Rational.UnipotentWoundCriterionCharPReduction
import Langlands.GroupScheme.Rational.UnipotentWoundCriterionCharZero

/-! # All-field assembly of the central additive-subgroup criterion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.UnipotentWoundCriterionReduction

/-- The remaining positive-characteristic inputs imply the unchanged all-field
criterion; characteristic zero uses its unconditional proof. -/
theorem criterion_of_structural_inputs
    (hP : Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement.{u,u})
    (hFactor : RelativeRoot.CommutativePTorsionVectorFactorStatement.{u}) :
    UnipotentWoundCriterionStatement.{u} := by
  intro k _ G hs ha hc hU
  let : Smooth G.X.hom := hs
  let : IsAffineHom G.X.hom := ha
  let : ConnectedSpace G.X.left := hc
  rcases CharP.exists' k with hzero | ⟨p, hp, hchar⟩
  · let : CharZero k := hzero
    exact criterion_of_charZero hU
  · let : Fact p.Prime := hp
    let : CharP k p := hchar
    exact criterion_of_charP hP hFactor p hU

/-- Choose an actual central closed additive line over any field, with the two
positive-characteristic prerequisites explicit. -/
def centralAdditiveLineOfStructuralInputs
    (hP : Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement.{u,u})
    (hFactor : RelativeRoot.CommutativePTorsionVectorFactorStatement.{u})
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hU : IsUnipotent G) (hG : ¬ HasConstantAffineLineMaps G) :
    Σ L : GroupScheme (Spec (CommRingCat.of k)),
      {j : L ⟶ G // IsClosedSubgroup j ∧ IsCentral j ∧
        RelativeRoot.IsVectorGroupOfDimension L 1} :=
  Classical.choice (by
    have h := (criterion_of_structural_inputs hP hFactor k G
      inferInstance inferInstance inferInstance hU).not.mp hG
    obtain ⟨L, j, hj, hcent, hL⟩ := Classical.not_not.mp h
    exact ⟨⟨L, j, hj, hcent, hL⟩⟩)

end Langlands.GroupScheme.UnipotentWoundCriterionReduction
