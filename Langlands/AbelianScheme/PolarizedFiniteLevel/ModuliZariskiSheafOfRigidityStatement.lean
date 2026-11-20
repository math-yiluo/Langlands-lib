import Langlands.AbelianScheme.PolarizedFiniteLevel.Functor
import Langlands.AbelianScheme.PolarizedFiniteLevel.LevelBaseZariski

/-! # Rigidity of polarized automorphisms implies the Zariski sheaf property -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- Fix `P`, positive `d` and a level `n ≥ 3`. If every polarized automorphism of every
ordinary polarized full-level datum over every level base is the identity, then the moduli
functor `moduliFunctor P g d n hd hn` satisfies the Zariski sheaf condition on level bases.
This proposition is a statement, not a proof of it. -/
def ModuliZariskiSheafOfRigidityStatement : Prop :=
  ∀ (P : Prerequisites.{0}) (g d n : ℕ) (hd : 0 < d) (hn : 3 ≤ n),
    (∀ (S : LevelBase n) (a : Datum P S.obj g d n) (α : PolarizedIso a a),
      α = PolarizedIso.refl a) →
    LevelBase.IsZariskiSheaf (moduliFunctor P g d n hd hn)

end Langlands.AbelianScheme.PolarizedFiniteLevel
