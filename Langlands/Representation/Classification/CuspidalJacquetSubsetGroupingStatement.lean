import Langlands.Representation.Classification.AdjacentCuspidalJacquetInterchangeStatement

/-! Actual grouping of a finite subset of cuspidal Jacquet factors. -/

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Adjacent actual interchange groups any selected subset of block labels
first when every outside-to-inside binary pair is irreducible and commutes.
The permutation retains all factors, including repetitions and unequal ranks. -/
def CuspidalJacquetSubsetGrouping : Prop :=
  AdjacentCuspidalJacquetInterchange.{uF, uV} F T →
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape n)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    π.IsIrreducible → π.IsAdmissible → π.HasFiniteLength →
    ∀ A : ∀ i, SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := B.size i),
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject (fun i => (A i).obj))
        ((T.normalizedJacquetFunctor B).obj π) →
      ∀ S : Finset (Fin B.length),
        (∀ i j : Fin B.length, i ∉ S → j ∈ S →
          ((T.binaryNormalizedProductFunctor (B.size i) (B.size j)).obj
            ((A i).obj, (A j).obj)).IsIrreducible ∧
          Nonempty ((T.binaryNormalizedProductFunctor (B.size i) (B.size j)).obj
              ((A i).obj, (A j).obj) ≅
            (Derivative.generalLinearRankCast T (Nat.add_comm (B.size j) (B.size i))).obj
              ((T.binaryNormalizedProductFunctor (B.size j) (B.size i)).obj
                ((A j).obj, (A i).obj)))) →
        ∃ e : Equiv.Perm (Fin B.length),
          (∀ i : Fin B.length, (i : ℕ) < S.card ↔ e i ∈ S) ∧
          SmoothRep.IsSubquotient
            (FiniteTensor.externalSmoothObject (fun i => (A (e i)).obj))
            ((T.normalizedJacquetFunctor (B.permute e)).obj π)

end Langlands.Classification
