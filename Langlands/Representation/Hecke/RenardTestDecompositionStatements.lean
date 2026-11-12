import Langlands.Representation.Hecke.DoubleCoset
import Langlands.Representation.Hecke.CommonInvarianceProof

/-! # Renard II.3.5: finite double-coset and coset expansions of tests -/

set_option autoImplicit false

open scoped BigOperators

universe uG

namespace Langlands.Hecke.RenardTestDecomposition

open Langlands.HarmonicAnalysis

/-- II.3.5 Lemma (i): a finite expansion with distinct double cosets. -/
def DoubleCosetExpansionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (f : SchwartzBruhat G),
      ∃ (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
        (n : ℕ) (g : Fin n → G) (c : Fin n → ℂ),
        Pairwise (fun i j =>
          Disjoint (TestFunction.doubleCosetSet K (g i))
            (TestFunction.doubleCosetSet K (g j))) ∧
        f = ∑ i, c i • TestFunction.doubleCosetIndicator K hK (g i)

/-- II.3.5 Lemma (ii), left invariance: support and expansion by the
right cosets `K g`. The empty family covers the zero test. -/
def LeftInvariantExpansionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (K : OpenSubgroup G), IsCompact (K : Set G) →
      ∀ f : SchwartzBruhat G, (∀ k : K, TestFunction.leftTranslate (k : G) f = f) →
        ∃ (n : ℕ) (g : Fin n → G) (c : Fin n → ℂ),
          (∀ i, c i ≠ 0) ∧
          Pairwise (fun i j =>
            Disjoint {x | ∃ k : K, x = (k : G) * g i}
              {x | ∃ k : K, x = (k : G) * g j}) ∧
          Function.support (f : G → ℂ) = ⋃ i, {x | ∃ k : K, x = (k : G) * g i} ∧
          ∀ x : G, f x = ∑ i, c i *
            ({y | ∃ k : K, y = (k : G) * g i} : Set G).indicator (fun _ => 1) x

/-- II.3.5 Lemma (ii), right invariance: support and expansion by
the left cosets `g K`. -/
def RightInvariantExpansionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (K : OpenSubgroup G), IsCompact (K : Set G) →
      ∀ f : SchwartzBruhat G, (∀ k : K, TestFunction.rightTranslate (k : G) f = f) →
        ∃ (n : ℕ) (g : Fin n → G) (c : Fin n → ℂ),
          (∀ i, c i ≠ 0) ∧
          Pairwise (fun i j =>
            Disjoint {x | ∃ k : K, x = g i * (k : G)}
              {x | ∃ k : K, x = g j * (k : G)}) ∧
          Function.support (f : G → ℂ) = ⋃ i, {x | ∃ k : K, x = g i * (k : G)} ∧
          ∀ x : G, f x = ∑ i, c i *
            ({y | ∃ k : K, y = g i * (k : G)} : Set G).indicator (fun _ => 1) x

def Statements : Prop :=
  DoubleCosetExpansionStatement.{uG} ∧
    LeftInvariantExpansionStatement.{uG} ∧ RightInvariantExpansionStatement.{uG}

end Langlands.Hecke.RenardTestDecomposition
