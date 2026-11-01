import Langlands.Geometry.Analytic.StrictTestDomain.AllUnitStandardRationalGluingStatement
import Langlands.Geometry.Analytic.StrictTestDomain.AllUnitLaurentRefinement
import Langlands.Geometry.Analytic.StrictTestDomain.IteratedLaurentScalarDescentProof

/-! # The all-unit case of scalar standard rational descent -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain

open RationalData

private def allUnitChoicesEquiv (n : ℕ) (hn : 0 < n) :
    AllUnitLaurentIndex n ≃ (Fin (n*n) → Bool) where
  toFun a := a.val
  invFun ε := ⟨ε, hn⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

/-- Unique scalar lifting for the actual standard cover of an all-unit tuple. -/
theorem allUnitStandardRationalGluing : AllUnitStandardRationalGluingStatement.{u} := by
  intro K _ _ _ P n f hf hu
  cases n with
  | zero =>
      let := subsingleton_of_empty_tuple f hf
      intro s _
      exact ⟨0, fun i => Fin.elim0 i, fun _ _ => Subsingleton.elim _ _⟩
  | succ n =>
      let e := allUnitChoicesEquiv (n+1) (Nat.zero_lt_succ n)
      have hE : ScalarCoverDescent (allUnitLaurentLeaf f) :=
        (scalarCoverDescent_iteratedLaurent ((n+1)*(n+1)) P (allUnitRatios f)).reindex e
      have hEu : UniversalScalarCoverDescent (allUnitLaurentLeaf f) :=
        (iteratedLaurentScalarDescent K P ((n+1)*(n+1)) (allUnitRatios f)).reindex e
      exact ScalarCoverDescent.of_refinement (standardRational f hf)
        (allUnitLaurentLeaf f) allUnitLaurentIndex (allUnitLaurentInclusion f hf hu)
        hE (fun i => (hEu _ (standardRational f hf i).baseMap).separated)

end Langlands.Analytic.StrictTestDomain
