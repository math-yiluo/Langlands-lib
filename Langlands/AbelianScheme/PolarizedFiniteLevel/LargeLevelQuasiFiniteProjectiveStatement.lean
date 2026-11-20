import Langlands.AbelianScheme.PolarizedFiniteLevel.Functor
import Langlands.AbelianScheme.PolarizedFiniteLevel.LocalizationBase
import Langlands.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Eventual locally quasi-finite maps from fine moduli schemes of ordinary polarized
full-level data to projective space -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- For positive dimension and polarization index and every sufficiently large level
`n ≥ 3`, every level base representing the ordinary polarized full-level moduli functor
admits a locally quasi-finite morphism over `Spec ℤ[1/n]` to a finite projective space.
This proposition is a statement, not a proof of it. -/
def LargeLevelQuasiFiniteProjectiveStatement : Prop :=
  ∀ (P : Prerequisites.{0}) (g d : ℕ) (_hg : 0 < g) (hd : 0 < d),
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n → ∀ (hn : 3 ≤ n) (X : LevelBase n),
      Nonempty (uliftYoneda.{1}.obj X ≅ moduliFunctor P g d n hd hn) →
        ∃ (m : ℕ)
          (j : X.obj ⟶
            Langlands.AlgebraicGeometry.ProjectiveSpace (Localization.Away (n : ℤ)) m),
          LocallyQuasiFinite j ∧
            j ≫ Langlands.AlgebraicGeometry.projectiveSpaceToSpec
              (Localization.Away (n : ℤ)) m = X.toLocalizationSpec

end Langlands.AbelianScheme.PolarizedFiniteLevel
