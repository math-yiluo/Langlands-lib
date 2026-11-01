import Langlands.Representation.Classification.IntegralCuspidalJacquetWord
import Langlands.Representation.Classification.Tempered

/-! # Integral cuspidal Jacquet words for analytic discrete series -/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- Every positive-rank irreducible analytically square-integrable smooth
representation has an actual nonempty cuspidal Jacquet word on one integral
line. The actual supercuspidal base is not required to be unitary. -/
def SquareIntegrableIntegralCuspidalJacquetWordExistence : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      Representation.IsIrreducible π.representation →
      T.IsSquareIntegrable π.representation →
      ∃ (m : ℕ), 0 < m ∧
        ∃ (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := m))
          (w : List ℤ),
          w ≠ [] ∧ IntegralCuspidalJacquetWord F T m n A π w

end Langlands.Classification
