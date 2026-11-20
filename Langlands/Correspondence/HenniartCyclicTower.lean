import Langlands.Correspondence.HenniartCyclicBaseChange

namespace Langlands.Henniart

open Langlands.Correspondence

universe uK

namespace Numerical

variable {p : ℕ} [Fact p.Prime]

/-- A nonempty tower of cyclic prime-degree extensions that carries a slope
below the absolute ramification index of the final field. -/
inductive ReachesCloseRange : PadicField.{uK} p → ℝ → Prop where
  /-- The first step already reaches the required range. -/
  | last (S : CyclicPrimeStep.{uK} p) (x : ℝ) :
      S.herbrandPsi x < S.top.canonicalTopologicalData.ramificationIndex →
        ReachesCloseRange S.base x
  /-- Continue from the top field with the slope given by the Herbrand function. -/
  | step (S : CyclicPrimeStep.{uK} p) (x : ℝ) :
      ReachesCloseRange S.top (S.herbrandPsi x) → ReachesCloseRange S.base x

end Numerical

/-- The tower lemma of the numerical local Langlands route note (§6.6,
`lem:tower`) for every nonnegative real slope over a p-adic field. -/
def CyclicTowerStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (x : ℝ), 0 ≤ x →
    Numerical.ReachesCloseRange K x

end Langlands.Henniart
