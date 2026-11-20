import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionConfiguration
import Langlands.AbelianScheme.PolarizedFiniteLevel.LocalizationBase
import Langlands.AlgebraicGeometry.ProjectiveSpace

/-! # Torsion bracket maps to projective space with finitely many configurations in each
geometric fibre -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- For positive dimension and polarization index and every sufficiently large level `n`,
every datum over a level base `T` admits a morphism `j` from `T` to a finite projective space
over `Spec ℤ[1/n]` with the following property. For every algebraically closed field `K` and
every `K`-point `y` of the projective space, there is a finite set `s` of `K`-points of `T`
such that the pullback of the datum along every `K`-point `t` of `T` with `t ≫ j = y` has a
torsion configuration equivalent to that of its pullback along some member of `s`.
This proposition is a statement, not a proof of it. -/
def TorsionBracketMapStatement : Prop :=
  ∀ (P : Prerequisites.{0}) (g d : ℕ), 0 < g → 0 < d →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (T : LevelBase n) (b : Datum P T.obj g d n),
      ∃ (m : ℕ)
        (j : T.obj ⟶
          Langlands.AlgebraicGeometry.ProjectiveSpace (Localization.Away (n : ℤ)) m),
        ∀ (K : Type) [Field K] [IsAlgClosed K]
          (y : Spec (CommRingCat.of K) ⟶
            Langlands.AlgebraicGeometry.ProjectiveSpace (Localization.Away (n : ℤ)) m),
          ∃ s : Finset (Spec (CommRingCat.of K) ⟶ T.obj),
            ∀ t : Spec (CommRingCat.of K) ⟶ T.obj, t ≫ j = y →
              ∃ t' ∈ s, (b.pullback t).TorsionConfigurationEquivalent (b.pullback t')

end Langlands.AbelianScheme.PolarizedFiniteLevel
