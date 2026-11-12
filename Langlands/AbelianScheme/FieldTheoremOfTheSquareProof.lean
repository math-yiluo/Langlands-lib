import Langlands.AbelianScheme.FieldTheoremOfTheSquareStatement
import Langlands.AbelianScheme.FieldCubePullbackProof
import Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroReduction
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof

/-! # The theorem of the square from the balanced cube

The unconditional theorem applies the square adapter to the published balanced
cube pullback theorem for actual line bundles over arbitrary fields.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AbelianScheme.MumfordPicardZero
open Langlands.AlgebraicGeometry.Picard

/-- The balanced cube identity implies the theorem of the square. -/
theorem fieldTheoremOfTheSquare_of_cube (cube : FieldCubePullbackStatement.{u}) :
    FieldTheoremOfTheSquareStatement.{u} := by
  intro K _ G _ hs hp hc L a b
  obtain ⟨cubeIso⟩ := cube K G hs hp hc G.X
    (Over.mkIdTerminal.from G.X ≫ a) (Over.mkIdTerminal.from G.X ≫ b) (𝟙 G.X) L
  exact ⟨Langlands.AbelianScheme.MumfordPicardZero.tensorIsoOf
      (pullbackCompIso (translation G b).left (translation G a).left
        (translation G (a * b)).left
        (by rw [← Over.comp_left, points_translation, translation, translation,
          MonObj.comp_mul, mul_assoc]) L.obj)
      (Iso.refl _) ≪≫
    squareIso fieldLineBundleTriviality G a b L cubeIso⟩

/-- The theorem of the square for actual line bundles on a commutative smooth,
proper, geometrically connected group scheme over an arbitrary field. -/
theorem fieldTheoremOfTheSquare : FieldTheoremOfTheSquareStatement.{u} :=
  fieldTheoremOfTheSquare_of_cube fieldCubePullback.{u}

end Langlands.GroupScheme
