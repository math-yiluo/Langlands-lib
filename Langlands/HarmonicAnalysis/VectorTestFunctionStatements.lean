import Langlands.HarmonicAnalysis.VectorTestFunction
import Langlands.Representation.Hecke.TestFunction
import Langlands.Topology.LocallyProfinite

/-! # Renard II.1.2: vector-valued indicators and tensor-map properties -/

set_option autoImplicit false

open scoped BigOperators

universe uX uV

namespace Langlands.HarmonicAnalysis.VectorTestFunctionStatements

open VectorTestFunction

/-- Every vector-valued compact test is a finite sum over disjoint compact opens. -/
def DisjointIndicatorDecomposition : Prop :=
  ∀ (X : Type uX) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (f : Space X V),
    ∃ (n : ℕ) (U : Fin n → Set X) (hUo : ∀ i, IsClopen (U i))
      (hUc : ∀ i, IsCompact (U i)) (v : Fin n → V),
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      f = ∑ i, compactBilinear
        (Langlands.Hecke.TestFunction.characteristic (hUo i) (hUc i)) (v i)

/-- Injectivity of the actual canonical algebraic tensor map in (II.1.2.3). -/
def SmoothTensorInjective : Prop :=
  ∀ (X : Type uX) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] (V : Type uV) [AddCommGroup V] [Module ℂ V],
    Function.Injective (smoothTensorMap (X := X) (V := V))

/-- Injectivity of the actual canonical compact tensor map in (II.1.2.4). -/
def CompactTensorInjective : Prop :=
  ∀ (X : Type uX) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] (V : Type uV) [AddCommGroup V] [Module ℂ V],
    Function.Injective (compactTensorMap (X := X) (V := V))

/-- Surjectivity of (II.1.2.4), asserted after the vector-valued decomposition. -/
def CompactTensorSurjective : Prop :=
  ∀ (X : Type uX) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] (V : Type uV) [AddCommGroup V] [Module ℂ V],
    Function.Surjective (compactTensorMap (X := X) (V := V))

/-- The vector-valued decomposition and the three canonical tensor-map assertions. -/
def Assertions : Prop :=
  DisjointIndicatorDecomposition.{uX, uV} ∧
    SmoothTensorInjective.{uX, uV} ∧
    CompactTensorInjective.{uX, uV} ∧ CompactTensorSurjective.{uX, uV}

end Langlands.HarmonicAnalysis.VectorTestFunctionStatements
