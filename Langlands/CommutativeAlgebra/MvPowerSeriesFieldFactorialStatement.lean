import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-! # Formal power series in finitely many variables over a field are factorial -/

universe u v

namespace Langlands.CommutativeAlgebra

/-- For every field `K` and every finite type `σ`, the ring `MvPowerSeries σ K` of formal power
series over `K` in the variables indexed by `σ` is a unique factorization monoid. This is a
derived special case of Stacks Remark 10.160.9 (Tag 032C: `k[[X_1, ..., X_d]]` is a regular local
ring) and Lemma 15.123.2 (Tag 0AG0: a regular local ring is a UFD). -/
def MvPowerSeriesFieldFactorial : Prop :=
  ∀ (K : Type u) [Field K] (σ : Type v) [Finite σ],
    UniqueFactorizationMonoid (MvPowerSeries σ K)

end Langlands.CommutativeAlgebra
