import Langlands.Representation.Geometric.ParabolicOrbitJacquet
import Langlands.AllField.Representation.Geometric.ParabolicSupportFiltration
/-! Actual normalized radical coinvariants of a compactly induced orbit piece. -/

noncomputable section
open CategoryTheory
open scoped NNReal

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic
open Langlands.AllField.Parabolic

universe uF uV


end Langlands.AllField.Parabolic

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricPieceFunctor jacquetInductionFunctor parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor
open Langlands.AllField.Geometric

universe uR uG uF uV

section RawOrbit


end RawOrbit

open Langlands.GeneralLinear

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B C : BlockShape n)

/-- The actual compact orbit piece for normalized parabolic induction, followed
by normalized radical coinvariants for the target parabolic. The orbit is
`P_B * w⁻¹ * P_C`, so the stabilizer representation uses conjugation by `w⁻¹`. -/
def parabolicOrbitJacquetFunctor (w : Equiv.Perm (Fin n)) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F) ⥤
      Rep.{max uF uV} ℂ (C.Levi F) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact B.inducingFunctor (T.leviHalfCharacter B) ⋙
    rawOrbitPiece (B.parabolic F) (C.parabolic F)
      (permutation n F w) ⋙
    Parabolic.normalizedCoinvariantsFunctor C (T.leviModulus C)

end Langlands.AllField.Geometric
