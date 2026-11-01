import Langlands.Representation.Classification.IntegralCuspidalJacquetWord
import Langlands.Representation.Classification.AdjacentCuspidalJacquetInterchangeStatement
import Langlands.Representation.Classification.RepeatedCuspidalTripleJacquetTransferStatement
import Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement

/-! # Conditional local moves for actual integral cuspidal Jacquet words -/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- Actual interchange, nonadjacent irreducibility and repeated-factor transfer
imply the three local closures for words realized on a fixed integral line. -/
def IntegralCuspidalJacquetWordLocalMoves : Prop :=
  AdjacentCuspidalJacquetInterchange.{uF,uV} F T →
  TwoSupercuspidalNonadjacentProductIrreducible.{uF, max uF uV} F T →
  RepeatedCuspidalTripleJacquetTransfer.{uF,uV} F T →
  letI := T.topology
  ∀ (m n : ℕ)
    (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := m))
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    π.IsIrreducible → π.IsAdmissible → π.HasFiniteLength →
    let P := IntegralCuspidalJacquetWord F T m n A π
    (∀ (l r : List ℤ) (a b : ℤ),
      a + 1 ≠ b → b + 1 ≠ a →
      P (l ++ [a, b] ++ r) → P (l ++ [b, a] ++ r)) ∧
    (∀ (l r : List ℤ) (b : ℤ),
      P (l ++ [b + 1, b, b] ++ r) → P (l ++ [b, b + 1, b] ++ r)) ∧
    (∀ (l r : List ℤ) (b : ℤ),
      P (l ++ [b + 1, b, b + 1] ++ r) →
        P (l ++ [b + 1, b + 1, b] ++ r) ∨
        P (l ++ [b, b + 1, b + 1] ++ r))

end Langlands.Classification
