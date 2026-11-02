import Langlands.Global.Factors.MeromorphicPoleComparisonStatement

/-!
# Pole comparison through finite analytic units
-/

noncomputable section

open Filter
open scoped Topology

namespace Langlands.Global.PoleComparison

universe u v

theorem omittedProduct_holomorphicUnitAt {A : Type u} (S : Finset A)
    (f : A → ℂ → ℂ) (z : ℂ) (h : OmittedUnitsAt S f z) :
    HolomorphicUnitAt (omittedProduct S f) z := by
  refine ⟨S.analyticAt_fun_prod (fun a ha => (h a ha).1), ?_⟩
  exact Finset.prod_ne_zero_iff.mpr (fun a ha => (h a ha).2)

theorem finiteOmittedOrder (A : Type u) : FiniteOmittedOrderStatement A := by
  intro S localFactor omitted boundary z homitted hboundary
  have hu := omittedProduct_holomorphicUnitAt S omitted z homitted
  change meromorphicOrderAt (boundary * (omittedProduct S omitted * localFactor)) z =
    meromorphicOrderAt localFactor z
  rw [meromorphicOrderAt_mul_of_ne_zero hboundary.1 hboundary.2,
    meromorphicOrderAt_mul_of_ne_zero hu.1 hu.2]

theorem completedPoleTransfer (A : Type u) (B : Type v) :
    CompletedPoleTransferStatement A B := by
  intro S T left right leftOmitted rightOmitted leftBoundary rightBoundary z
    _ _ hleft hright hleftBoundary hrightBoundary hcompleted
  rw [← finiteOmittedOrder A S left leftOmitted leftBoundary z hleft hleftBoundary,
    ← finiteOmittedOrder B T right rightOmitted rightBoundary z hright hrightBoundary]
  exact meromorphicOrderAt_congr hcompleted

theorem meromorphicPoleComparison (A : Type u) (B : Type v) :
    MeromorphicPoleComparisonStatement A B :=
  ⟨finiteOmittedOrder A, finiteOmittedOrder B, completedPoleTransfer A B⟩

end Langlands.Global.PoleComparison
