import Langlands.Global.ArchimedeanHilbertSchmidt
import Langlands.Automorphic.Growth

/-!
# Comparison of actual archimedean matrix height and Hilbert-Schmidt growth

These proposition definitions state the remaining comparison obligation.
They reuse the published norms and growth predicates at every natural rank.
-/

universe u

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Positive comparison constants are uniform over the actual infinite group. -/
def ArchimedeanMatrixHilbertComparisonStatement : Prop :=
  ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ g : InfiniteAdelicGL K n,
    ArchimedeanGL.matrixHeight K n g ≤ C * infiniteAdelicHilbertNorm K n g ∧
    infiniteAdelicHilbertNorm K n g ≤ D * ArchimedeanGL.matrixHeight K n g

/-- The existing matrix-growth predicate agrees with Hilbert-Schmidt growth
for every complex-valued function, without a regularity hypothesis. -/
def ArchimedeanHilbertGrowthEquivalenceStatement : Prop :=
  ∀ f : InfiniteAdelicGL K n → ℂ,
    ArchimedeanGL.HasPolynomialGrowth K n f ↔
      ∃ B : ℝ, 0 ≤ B ∧ ∃ d : ℕ, ∀ g : InfiniteAdelicGL K n,
        ‖f g‖ ≤ B * infiniteAdelicHilbertNorm K n g ^ d

/-- The adelic equivalence chooses a separate bound and exponent on each finite slice. -/
def AdelicHilbertGrowthEquivalenceStatement : Prop :=
  ∀ f : Langlands.Automorphic.ContinuousRationalFunctions K n,
    Langlands.Automorphic.HasPolynomialGrowth K n f ↔
      ∀ b : FiniteAdelicGL K n, ∃ B : ℝ, 0 ≤ B ∧ ∃ d : ℕ,
        ∀ g : InfiniteAdelicGL K n,
          ‖Langlands.Automorphic.infiniteSlice K n b f g‖ ≤
            B * infiniteAdelicHilbertNorm K n g ^ d

/-- Aggregate target for linear norm comparison and both polynomial-growth equivalences.
The number field has arbitrary universe and the natural rank may be zero. -/
def ArchimedeanHilbertGrowthComparisonStatement : Prop :=
  ArchimedeanMatrixHilbertComparisonStatement K n ∧
  ArchimedeanHilbertGrowthEquivalenceStatement K n ∧
  AdelicHilbertGrowthEquivalenceStatement K n

end Langlands.Global
