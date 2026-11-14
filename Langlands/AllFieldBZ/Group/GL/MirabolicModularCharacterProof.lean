import Langlands.AllFieldBZ.Group.GL.MirabolicModulusProof
import Langlands.AllFieldBZ.Group.GL.MirabolicProjection
import Langlands.Group.GL.MirabolicModularCharacterProof

/-!
# All-field port of `Langlands.Group.GL.MirabolicModularCharacterProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.MirabolicModularCharacterProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ
open MeasureTheory
open Measure
open Set
open TopologicalSpace
open scoped NNReal
open scoped ENNReal
universe uF

namespace GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic hiding leviRadical_haarCharacter radicalCoordinates_isAddHaar radicalHaar_map_leviConj
section Algebra
variable {K : Type uF} [Field K] {n : ℕ}

private theorem _root_.Langlands.GeneralLinear.Mirabolic.det_lastRow (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hA : ∀ j, A (Fin.last n) j = if j = Fin.last n then 1 else 0) :
    Matrix.det A = Matrix.det (A.submatrix Fin.castSucc Fin.castSucc) := by
  rw [Matrix.det_succ_row A (Fin.last n)]
  simp only [hA, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp [Fin.succAbove_last, ← two_mul, pow_mul]

end Algebra
section Topology
variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}

end Topology
end GeneralLinear.Mirabolic
end Langlands.AllFieldBZ
