import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionConfiguration

/-! # At large level, torsion configurations determine data over algebraically closed fields -/

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- For positive dimension and polarization index there is a bound `N` such that, for every
level `n ≥ N` and every algebraically closed field in which `n` is nonzero, two data whose
torsion configurations are equivalent are isomorphic.
This proposition is a statement, not a proof of it. -/
def TorsionConfigurationDeterminationStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (g d : ℕ), 0 < g → 0 < d →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (K : Type u) [Field K] [IsAlgClosed K], (n : K) ≠ 0 →
        ∀ a b : Datum P (Spec (CommRingCat.of K)) g d n,
          a.TorsionConfigurationEquivalent b → Isomorphic a b

end Langlands.AbelianScheme.PolarizedFiniteLevel
