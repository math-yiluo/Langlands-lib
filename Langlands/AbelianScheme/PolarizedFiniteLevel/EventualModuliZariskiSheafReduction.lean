import Langlands.AbelianScheme.PolarizedFiniteLevel.EventualModuliZariskiSheafStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.ModuliZariskiSheafOfRigidityStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.GeometricPointRigidity

/-! # The eventual Zariski sheaf property from Lefschetz's theorem and gluing -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

set_option linter.defProp false in
/-- Proved definition: Lefschetz's embedding theorem over fields and the gluing statement
`ModuliZariskiSheafOfRigidityStatement` imply `EventualModuliZariskiSheafStatement`, with the
bound `N = (6^g*d) * (6^g*d*g!) + 1`. At such levels every polarized automorphism over every
level base is the identity (`PolarizedIso.eq_refl_of_cubicFieldEmbedding`). -/
def eventualModuliZariskiSheaf_of_rigidity (hL : CubicFieldEmbeddingStatement.{0})
    (hG : ModuliZariskiSheafOfRigidityStatement) : EventualModuliZariskiSheafStatement := by
  intro P g d hg hd
  refine ⟨(cubicProjectiveDimension g d + 1) * (6 ^ g * d * Nat.factorial g) + 1, ?_⟩
  intro n hN hn
  have hlt : (cubicProjectiveDimension g d + 1) * (6 ^ g * d * Nat.factorial g) < n := hN
  exact hG P g d n hd hn fun S a α =>
    α.eq_refl_of_cubicFieldEmbedding hL hg hd hlt S.level_isUnit

end Langlands.AbelianScheme.PolarizedFiniteLevel
