import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.Characters
import Mathlib.NumberTheory.LocalField.Basic

/-! # Rational-point decompositions for compatible represented parabolics

This is the structural input to represented-parabolic transitivity in Renard 2026,
VI.1.4. The three parabolic triples are supplied; their containment and intersection
are specified on rational points. No dynamic presentation or radical decomposition
is assumed.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

/-- Compatible actual rational parabolic triples over a nonarchimedean local field have
the inner radical and the two product decompositions of Renard VI.1.4. -/
def NestedParabolicPointDecompositionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (_hG : IsConnectedReductive G)
    (P M N Q L U PL NL : GroupScheme (Spec (CommRingCat.of k)))
    (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
    (_hp : IsParabolicSubgroup p) (_hm : IsRationalLeviSubgroup m)
    (_hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (_hmul : IsIso (subgroupMultiplication m n))
    (q : Q ⟶ G) (l : L ⟶ Q) (uQ : U ⟶ Q)
    (_hq : IsParabolicSubgroup q) (_hl : IsRationalLeviSubgroup l)
    (_huQ : LeviSubgroup.IsGeometricUnipotentRadical uQ)
    (_hmulQ : IsIso (subgroupMultiplication l uQ))
    (pL : PL ⟶ L) (mL : M ⟶ PL) (nL : NL ⟶ PL)
    (_hpL : IsParabolicSubgroup pL) (_hmL : IsRationalLeviSubgroup mL)
    (_hnL : LeviSubgroup.IsGeometricUnipotentRadical nL)
    (_hmulL : IsIso (subgroupMultiplication mL nL)),
    let P₀ := (rationalPoints.map p).range
    let Q₀ := (rationalPoints.map q).range
    let L₀ := (rationalPoints.map (l ≫ q)).range
    let N₀ := (rationalPoints.map (n ≫ p)).range
    let U₀ := (rationalPoints.map (uQ ≫ q)).range
    let PL₀ := (rationalPoints.map (pL ≫ l ≫ q)).range
    let NL₀ := (rationalPoints.map (nL ≫ pL ≫ l ≫ q)).range
    P₀ ≤ Q₀ →
    mL ≫ pL ≫ l ≫ q = m ≫ p →
    PL₀ = L₀ ⊓ P₀ →
      NL₀ = L₀ ⊓ N₀ ∧
        (N₀ : Set (rationalPoints G)) =
          ((L₀ ⊓ N₀ : Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
            (U₀ : Set (rationalPoints G)) ∧
        (P₀ : Set (rationalPoints G)) =
          (PL₀ : Set (rationalPoints G)) * (U₀ : Set (rationalPoints G))

end Langlands.GroupScheme
