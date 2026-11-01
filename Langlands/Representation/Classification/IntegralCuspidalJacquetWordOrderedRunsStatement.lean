import Langlands.Representation.Classification.IntegralCuspidalJacquetWord
import Langlands.Representation.Classification.AdjacentCuspidalJacquetInterchangeStatement
import Langlands.Representation.Classification.RepeatedCuspidalTripleJacquetTransferStatement
import Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Range

/-! # A least realized word and its ordered consecutive runs -/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- Conditional ordered-run decomposition within a fixed realized permutation
class, retaining actual Jacquet occurrence. -/
def IntegralCuspidalJacquetWordOrderedRuns : Prop :=
  AdjacentCuspidalJacquetInterchange.{uF,uV} F T →
  TwoSupercuspidalNonadjacentProductIrreducible.{uF, max uF uV} F T →
  RepeatedCuspidalTripleJacquetTransfer.{uF,uV} F T →
  letI := T.topology
  ∀ (m n : ℕ)
    (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := m))
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    π.IsIrreducible → π.IsAdmissible → π.HasFiniteLength →
    ∀ w₀ : List ℤ, IntegralCuspidalJacquetWord F T m n A π w₀ →
    ∃ w : List ℤ,
      IntegralCuspidalJacquetWord F T m n A π w ∧
      w.Perm w₀ ∧
      (∀ v : List ℤ, IntegralCuspidalJacquetWord F T m n A π v →
        v.Perm w₀ → ¬ List.Lex (· < ·) v w) ∧
      ∃ runs : List (ℤ × ℕ),
        (∀ s ∈ runs, 0 < s.2) ∧
        runs.IsChain (fun s t => s.1 ≤ t.1) ∧
        w = runs.flatMap (fun s =>
          (List.range s.2).map (fun j => s.1 - (j : ℤ)))

end Langlands.Classification
