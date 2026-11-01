import Langlands.HarmonicAnalysis.Distribution.Subspace
import Langlands.Representation.Hecke.TestFunction

/-! # Renard II.1.2: disjoint indicators and the open-closed exact sequences -/

set_option autoImplicit false

open scoped BigOperators

universe u

namespace Langlands.HarmonicAnalysis.TestFunctionDistributionStatements

/-- Every test function is a finite linear combination of disjoint compact-open indicators. -/
def DisjointIndicatorDecomposition : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] (f : SchwartzBruhat X),
    ∃ (n : ℕ) (V : Fin n → Set X) (hVo : ∀ i, IsClopen (V i))
      (hVc : ∀ i, IsCompact (V i)) (c : Fin n → ℂ),
      Pairwise (fun i j => Disjoint (V i) (V j)) ∧
      f = ∑ i, c i • Langlands.Hecke.TestFunction.characteristic (hVo i) (hVc i)

/-- Exactness of 0 → D(U) → D(X) → D(Uᶜ) → 0, using the original maps. -/
def TestFunctionExactSequence : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] (U : Set X) (hU : IsOpen U),
    Function.Injective (SchwartzBruhat.extendZero hU) ∧
    LinearMap.range (SchwartzBruhat.extendZero hU) =
      LinearMap.ker (SchwartzBruhat.restrictClosed hU.isClosed_compl) ∧
    Function.Surjective (SchwartzBruhat.restrictClosed hU.isClosed_compl)

/-- Exactness of 0 → D′(Uᶜ) → D′(X) → D′(U) → 0 in the full algebraic duals. -/
def DistributionExactSequence : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] (U : Set X) (hU : IsOpen U),
    Function.Injective (Distribution.closedPushforward hU.isClosed_compl) ∧
    LinearMap.range (Distribution.closedPushforward hU.isClosed_compl) =
      LinearMap.ker (Distribution.restrictOpen hU) ∧
    Function.Surjective (Distribution.restrictOpen hU)

/-- The scalar indicator lemma and both complete open-closed exact sequences. -/
def Assertions : Prop :=
  DisjointIndicatorDecomposition.{u} ∧
    TestFunctionExactSequence.{u} ∧ DistributionExactSequence.{u}

end Langlands.HarmonicAnalysis.TestFunctionDistributionStatements
