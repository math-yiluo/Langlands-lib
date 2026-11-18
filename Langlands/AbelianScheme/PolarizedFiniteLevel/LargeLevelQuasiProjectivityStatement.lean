import Langlands.AbelianScheme.PolarizedFiniteLevel.Functor
import Langlands.AbelianScheme.PolarizedFiniteLevel.LocalizationBase
import Langlands.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Eventual quasi-projectivity of any fine moduli scheme of ordinary polarized
full-level data -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- For positive dimension and polarization index and every sufficiently large
level `n ≥ 3`, every level base representing the ordinary polarized full-level
moduli functor is quasi-compact over `Spec ℤ[1/n]` and admits an immersion over
`Spec ℤ[1/n]` into a finite projective space. This proposition is a statement,
not a proof of it. -/
def LargeLevelQuasiProjectivityStatement : Prop :=
  ∀ (P : Prerequisites.{0}) (g d : ℕ) (_hg : 0 < g) (hd : 0 < d),
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n → ∀ (hn : 3 ≤ n) (X : LevelBase n),
      Nonempty (uliftYoneda.{1}.obj X ≅ moduliFunctor P g d n hd hn) →
        QuasiCompact X.toLocalizationSpec ∧
          ∃ (m : ℕ)
            (i : X.obj ⟶
              Langlands.AlgebraicGeometry.ProjectiveSpace (Localization.Away (n : ℤ)) m),
            IsImmersion i ∧
              i ≫ Langlands.AlgebraicGeometry.projectiveSpaceToSpec
                (Localization.Away (n : ℤ)) m = X.toLocalizationSpec

end Langlands.AbelianScheme.PolarizedFiniteLevel
