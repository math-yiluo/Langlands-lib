import Langlands.HarmonicAnalysis.Basic

/-!
# Finite tensor decomposition of row Schwartz–Bruhat functions

This internal proposition states finite generation by pointwise products of
one-coordinate test functions. It does not construct an abstract tensor product.
-/

namespace Langlands.HarmonicAnalysis

open scoped BigOperators

universe u

/-- Every row test function is a finite complex linear combination of products
of one-coordinate test functions, including in dimension zero. -/
def RowTensorDecompositionStatement (X : Type u) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] (d : ℕ) : Prop :=
  ∀ f : SchwartzBruhat (Fin d → X),
    ∃ (N : ℕ) (c : Fin N → ℂ) (g : Fin N → Fin d → SchwartzBruhat X),
      ∀ x : Fin d → X, f x = ∑ j : Fin N, c j * ∏ i : Fin d, g j i (x i)

end Langlands.HarmonicAnalysis
