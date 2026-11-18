import Langlands.AbelianScheme.PolarizedFiniteLevel.Functor
import Langlands.AbelianScheme.PolarizedFiniteLevel.LevelBaseZariski

/-! # The ordinary polarized full-level moduli functor is a Zariski sheaf for large levels -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- For positive dimension and polarization index, the published ordinary polarized
full-level moduli functor satisfies the Zariski sheaf condition on the level base category
for every sufficiently large level `n ≥ 3`. This proposition is a statement, not a proof
of it. -/
def EventualModuliZariskiSheafStatement : Prop :=
  ∀ (P : Prerequisites.{0}) (g d : ℕ) (_hg : 0 < g) (hd : 0 < d),
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n → ∀ (hn : 3 ≤ n),
      LevelBase.IsZariskiSheaf (moduliFunctor P g d n hd hn)

end Langlands.AbelianScheme.PolarizedFiniteLevel
