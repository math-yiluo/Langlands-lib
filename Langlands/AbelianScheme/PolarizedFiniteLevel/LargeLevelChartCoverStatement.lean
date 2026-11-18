import Langlands.AbelianScheme.PolarizedFiniteLevel.Functor
import Langlands.AbelianScheme.PolarizedFiniteLevel.LevelBaseZariski

/-! # Eventual open chart covers of ordinary polarized full-level moduli -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- For positive dimension and polarization index, every sufficiently large
level `n ≥ 3` admits a family of level bases whose functors of points are open
charts of the ordinary polarized full-level moduli functor and cover it.
This proposition is a statement, not a proof of it. -/
def LargeLevelChartCoverStatement : Prop :=
  ∀ (P : Prerequisites.{0}) (g d : ℕ) (_hg : 0 < g) (hd : 0 < d),
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n → ∀ (hn : 3 ≤ n),
      ∃ (ι : Type) (X : ι → LevelBase n)
        (a : ∀ i, uliftYoneda.{1}.obj (X i) ⟶ moduliFunctor P g d n hd hn),
        (∀ i, LevelBase.IsOpenChart (a i)) ∧ LevelBase.IsOpenChartCover a

end Langlands.AbelianScheme.PolarizedFiniteLevel
