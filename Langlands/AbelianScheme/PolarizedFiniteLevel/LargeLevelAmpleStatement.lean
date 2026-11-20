import Langlands.AbelianScheme.PolarizedFiniteLevel.Functor
import Langlands.AbelianScheme.PolarizedFiniteLevel.LocalizationBase
import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Eventual ample line bundles on fine moduli schemes of ordinary polarized
full-level data -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- For positive dimension and polarization index and every sufficiently large level
`n ≥ 3`, every level base representing the ordinary polarized full-level moduli functor is
locally of finite type over `Spec ℤ[1/n]` and carries an ample line bundle. This
proposition is a statement, not a proof of it. -/
def LargeLevelAmpleStatement : Prop :=
  ∀ (P : Prerequisites.{0}) (g d : ℕ) (_hg : 0 < g) (hd : 0 < d),
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n → ∀ (hn : 3 ≤ n) (X : LevelBase n),
      Nonempty (uliftYoneda.{1}.obj X ≅ moduliFunctor P g d n hd hn) →
        LocallyOfFiniteType X.toLocalizationSpec ∧
          ∃ L : Langlands.AlgebraicGeometry.Picard.LineBundle X.obj, L.IsAmple

end Langlands.AbelianScheme.PolarizedFiniteLevel
