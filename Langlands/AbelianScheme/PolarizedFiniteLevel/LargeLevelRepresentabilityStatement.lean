import Langlands.AbelianScheme.PolarizedFiniteLevel.Functor
import Langlands.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Eventual fine representability of ordinary polarized full-level moduli -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- For positive dimension and polarization index, sufficiently large full
levels admit an actual quasi-projective fine moduli scheme over `ℤ[1/n]`.
The scheme, embedding and natural representing isomorphism are conclusions.
This proposition is a statement of geometric existence, not a proof of it. -/
def LargeLevelRepresentabilityStatement : Prop :=
  ∀ (P : Prerequisites.{0}) (g d : ℕ) (_hg : 0 < g) (hd : 0 < d),
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n → ∀ (hn : 3 ≤ n),
      ∃ (X : LevelBase n)
        (π : X.obj ⟶ Spec (CommRingCat.of (Localization.Away (n : ℤ)))),
        QuasiCompact π ∧
        (∃ (m : ℕ)
          (i : X.obj ⟶
            Langlands.AlgebraicGeometry.ProjectiveSpace (Localization.Away (n : ℤ)) m),
          IsImmersion i ∧
            i ≫ Langlands.AlgebraicGeometry.projectiveSpaceToSpec
              (Localization.Away (n : ℤ)) m = π) ∧
        Nonempty (CategoryTheory.uliftYoneda.{1}.obj X ≅ moduliFunctor P g d n hd hn)

end Langlands.AbelianScheme.PolarizedFiniteLevel
