import Langlands.GroupScheme.Rational.LeviPreimageSolvableRadical
import Langlands.GroupScheme.Rational.ParabolicGeometricSolvableRadicalExistsStatement
import Langlands.GroupScheme.Rational.ReductiveGeometricSolvableRadicalExistsStatement

/-! # Geometric solvable radicals of parabolics from the structure theory -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The geometric solvable radical existence target for rational parabolics follows from the
dynamic description of parabolics, connected reductivity of dynamic centralizers and the
existence of geometric solvable radicals of connected reductive groups. -/
def ParabolicGeometricSolvableRadicalFromStructureStatement : Prop :=
  ParabolicDynamicStatement.{u} → DynamicCentralizerReductiveStatement.{u} →
    ReductiveGeometricSolvableRadicalExistsStatement.{u} →
      ParabolicGeometricSolvableRadicalExistsStatement.{u}

/-- A rational parabolic `P = P_G(χ)` has the rational Levi subgroup `Z_G(χ)`; the inverse
image of the geometric solvable radical of `Z_G(χ)` under the Levi retraction is a geometric
solvable radical of `P`. -/
theorem parabolicGeometricSolvableRadicalExists_of_structure :
    ParabolicGeometricSolvableRadicalFromStructureStatement.{u} := by
  intro hPD hCR hred k _ G hG P j hj
  obtain ⟨L, l, hl⟩ := hj.exists_isRationalLeviSubgroup hPD hCR hG
  obtain ⟨C, c, hc⟩ := hred k L hl.isConnectedReductive
  exact hl.exists_isGeometricSolvableRadical hc

end Langlands.GroupScheme
