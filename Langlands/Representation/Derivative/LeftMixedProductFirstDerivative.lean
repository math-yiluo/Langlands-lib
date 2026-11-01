import Langlands.Representation.Derivative.MirabolicProductMinusLeftPsi
import Langlands.Representation.Derivative.LeftMixedProductZeroRank

/-! The first derivative of an actual left mixed product, including GL rank zero. -/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The order-one instance of the left mixed-product derivative comparison,
with the exact source-rank derivative and target cast. -/
def leftMixedProductFirstDerivativeIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ) :
    letI := T.topology
    T.leftMixedProductFunctor.{uF, uV} k r ⋙
        mirabolicDerivativeOfOrder T ψ (k + r) 1 ⟨by omega, by omega⟩ ⋙
          generalLinearRankCast T
            (show k + r + 1 - 1 = k + (r + 1 - 1) by omega) ≅
      (𝟭 _).prod (mirabolicDerivativeOfOrder T ψ r 1 ⟨by omega, by omega⟩) ⋙
        T.binaryNormalizedProductFunctor k (r + 1 - 1) := by
  letI := T.topology
  cases k with
  | zero =>
      exact LeftMixedProductZeroRank.leftMixedProductZeroRankIso T ψ r 1
        ⟨by omega, by omega⟩
  | succ k =>
      simp only [mirabolicDerivativeOfOrder_one,
        generalLinearRankCast_refl, Functor.comp_id]
      exact Classical.choice
        (MirabolicProductMinus.leftPsiCompatibility.{uF, uV} T k r)

end Langlands.Derivative
