import Langlands.Representation.Classification.RelativeRegularComparisonStatement
import Langlands.Representation.Geometric.WeylDefinitions

/-! Weighted positive-root parameters have zero sums on actual nested blocks. -/

namespace Langlands.Exponents

open GeneralLinear Geometric RelativeRegularComparison
open scoped BigOperators

/-- The weighted fine-block sums, actual middle-coordinate sums, and transported
coarse-coordinate sums of the existing positive-root parameter are zero. -/
def PositiveRootBlockSumsStatement : Prop :=
  (∀ (n : ℕ) (D : BlockShape n) (R : BlockRefinement D)
      (v : Fin (D.flatten R).length → ℝ),
    IsPositiveRootParameter D R v →
    ∀ i : Fin D.length,
      ∑ k : Fin (R i).length,
        ((R i).size k : ℝ) * v (D.flattenBlockEquiv R ⟨i, k⟩) = 0) ∧
  (∀ (n : ℕ) (D : BlockShape n) (R : BlockRefinement D)
      (v : Fin (D.flatten R).length → ℝ),
    IsPositiveRootParameter D R v →
    ∀ i : Fin D.length,
      ∑ a : Fin (D.size i),
        v (blockIndex (D.flatten R) (D.index i a)) = 0) ∧
  (∀ (n : ℕ) (B : BlockShape n) (Q : BlockRefinement B)
      (R : BlockRefinement (B.flatten Q)) (S : BlockRefinement B)
      (h : (B.flatten Q).flatten R = B.flatten S)
      (v : Fin ((B.flatten Q).flatten R).length → ℝ),
    IsPositiveRootParameter (B.flatten Q) R v →
    ∀ i : Fin B.length,
      ∑ a : Fin (B.size i),
        (h ▸ v) (blockIndex (B.flatten S) (B.index i a)) = 0)

end Langlands.Exponents
