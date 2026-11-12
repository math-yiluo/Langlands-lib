import Langlands.Representation.Aubert.General.RationalGeometricK0Reduction
import Langlands.Representation.Aubert.General.RationalGeometricEpsilonBalance

/-!
# The rational geometric-lemma K0 expansion from the parabolic points statement

The epsilon cancellation `geometricEpsilon_mul_eq_one` discharges the balance
input of `geometricK0Expansion_of_points_of_balance`. What remains is exactly
the published `StandardParabolicPointsStatement`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

/-- The published target `RationalGeometricK0ExpansionStatement`, from the
published standard-parabolic points statement. -/
theorem rationalGeometricK0Expansion_of_standardParabolicPoints
    (hPoints : StandardParabolicPointsStatement.{u}) :
    RationalGeometricK0ExpansionStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro _ _ _ ν hν hStandard hRoots hU hP hproj hUc hiFl hrFl hM _ hN hZ CM cs _ _ hLevi hGeom
    hTermFl
  exact geometricK0Expansion_of_points_of_balance.{u, v} i ν hStandard hG hi hν hU hP hproj
    hUc hiFl hrFl hM hN hZ cs hLevi hGeom hTermFl hPoints
    (fun I J n => geometricEpsilon_mul_eq_one i ν hStandard hG hi hν hN hRoots I J _ _ n
      hU hP hM (hproj I) (hproj J))

set_option linter.defProp false in
/-- The reduction of `RationalGeometricK0ExpansionStatement` to
`StandardParabolicPointsStatement`, as a declaration whose type is the
implication. -/
def rationalGeometricK0ExpansionOfStandardParabolicPoints :
    StandardParabolicPointsStatement.{u} → RationalGeometricK0ExpansionStatement.{u, v} :=
  rationalGeometricK0Expansion_of_standardParabolicPoints

end Langlands.Aubert.General.RationalPointFamily
