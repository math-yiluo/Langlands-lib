import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocus
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicProjectiveEvaluation
import Langlands.AbelianScheme.PolarizedFiniteLevel.Functor

/-! # Representability of the projective frame charts of ordinary polarized moduli -/

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- For every level `n ≥ 3` and every tuple `ρ` of `6^g*d + 1` level coefficient
tuples, the classes of data whose frame locus for `ρ` is the whole base form a
subfunctor of the ordinary polarized full-level moduli functor represented by a
level base. This proposition is a statement, not a proof of it. -/
def FrameChartRepresentabilityStatement : Prop :=
  ∀ (P : Prerequisites.{0}) (g d n : ℕ) (hd : 0 < d) (hn : 3 ≤ n)
    (ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n),
    ∃ (X : LevelBase n) (a : uliftYoneda.{1}.obj X ⟶ moduliFunctor P g d n hd hn),
      (∀ T : (LevelBase n)ᵒᵖ, Function.Injective (a.app T)) ∧
        ∀ (T : LevelBase n) (b : Datum P T.obj g d n),
          b.classOf ∈ Set.range (a.app (op T)) ↔ b.frameLocus ρ = ⊤

end Langlands.AbelianScheme.PolarizedFiniteLevel
