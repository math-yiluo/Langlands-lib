import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocus
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicProjectiveEvaluation
import Langlands.AbelianScheme.PolarizedFiniteLevel.Functor
import Langlands.AbelianScheme.PolarizedFiniteLevel.LocalizationBase
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Eventual finite type of representing objects of the projective frame charts -/

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- For positive dimension and polarization index and every sufficiently large level
`n ≥ 3`, every projective frame chart of the ordinary polarized full-level moduli functor
is represented by a level base that is locally of finite type and quasi-compact over
`Spec ℤ[1/n]`. This proposition is a statement, not a proof of it. -/
def FrameChartFiniteTypeStatement : Prop :=
  ∀ (P : Prerequisites.{0}) (g d : ℕ) (_hg : 0 < g) (hd : 0 < d),
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n → ∀ (hn : 3 ≤ n)
      (ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n),
      ∃ (X : LevelBase n) (a : uliftYoneda.{1}.obj X ⟶ moduliFunctor P g d n hd hn),
        (∀ T : (LevelBase n)ᵒᵖ, Function.Injective (a.app T)) ∧
        (∀ (T : LevelBase n) (b : Datum P T.obj g d n),
          b.classOf ∈ Set.range (a.app (op T)) ↔ b.frameLocus ρ = ⊤) ∧
        LocallyOfFiniteType X.toLocalizationSpec ∧ QuasiCompact X.toLocalizationSpec

end Langlands.AbelianScheme.PolarizedFiniteLevel
