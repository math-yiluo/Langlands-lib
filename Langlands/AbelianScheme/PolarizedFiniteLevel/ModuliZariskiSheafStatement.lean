import Langlands.AbelianScheme.PolarizedFiniteLevel.Functor
import Langlands.AbelianScheme.PolarizedFiniteLevel.LevelBaseZariski

/-! # The ordinary polarized full-level moduli functor is a Zariski sheaf -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- For every level `n ≥ 3` and positive polarization index, the published ordinary
polarized full-level moduli functor satisfies the Zariski sheaf condition on the
level base category. This proposition is a statement, not a proof of it. -/
def ModuliZariskiSheafStatement : Prop :=
  ∀ (P : Prerequisites.{0}) (g d n : ℕ) (hd : 0 < d) (hn : 3 ≤ n),
    LevelBase.IsZariskiSheaf (moduliFunctor P g d n hd hn)

end Langlands.AbelianScheme.PolarizedFiniteLevel
