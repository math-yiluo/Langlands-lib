import Langlands.GroupScheme.IntegralModel.GreenbergMixed.Connected
import Langlands.GroupScheme.IntegralModel.GreenbergPointModelCases

/-! # Greenberg point models from a Greenberg ring scheme

A Greenberg coefficient ring scheme of level `n` over a local ring with algebraically closed
residue field yields the full point-model conclusion `HasGreenbergPointModel R n X` for every
smooth affine group scheme `X`. Hence the mixed-characteristic case of KP Theorem A.4.19
(points form) reduces to the existence of such ring schemes.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IntegralModel.GreenbergMixed

/-- **Point models from a ring scheme.** Every smooth affine group over `R` has a Greenberg
point model at level `n` once a Greenberg ring scheme of level `n` is given. -/
theorem hasGreenbergPointModel_of_ringScheme {R : Type u} [CommRing R] [IsLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] {n : ℕ+} (ℛ : GreenbergRingScheme R n)
    (X : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom X.X.hom] (hX : Smooth X.X.hom) :
    HasGreenbergPointModel R n X := by
  obtain ⟨P⟩ := nonempty_coordPres X hX
  refine ⟨greenbergGroup ℛ X P, levelPointsEquiv ℛ X P, inferInstance,
    smooth_greenbergGroup ℛ X P hX, ?_⟩
  intro Z _ hZ h
  obtain ⟨Q⟩ := nonempty_coordPres Z hZ
  refine ⟨greenbergGroup ℛ Z Q, levelPointsEquiv ℛ Z Q, greenbergMap ℛ X P Q h, inferInstance,
    smooth_greenbergGroup ℛ Z Q hZ, levelPointsEquiv_naturality ℛ X P Q h, ?_⟩
  intro hc
  have : GeometricallyConnected Z.X.hom := hc
  exact geometricallyConnected_greenbergGroup ℛ Z hZ Q

/-- Existence of Greenberg ring schemes over mixed-characteristic DVRs with algebraically
closed residue field, at every positive level. -/
def GreenbergRingSchemeExistence : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)],
    ringChar R ≠ ringChar (IsLocalRing.ResidueField R) →
    ∀ n : ℕ+, Nonempty (GreenbergRingScheme R n)

/-- **Reduction.** The mixed-characteristic Greenberg point-model statement follows from the
existence of Greenberg ring schemes. -/
theorem mixedCharacteristicGreenbergPointModel_of_existence
    (hex : GreenbergRingSchemeExistence.{u}) :
    MixedCharacteristicGreenbergPointModelStatement.{u} := by
  intro R _ _ _ _ hchar n X _ hX
  obtain ⟨ℛ⟩ := hex R hchar n
  exact hasGreenbergPointModel_of_ringScheme ℛ X hX

end Langlands.GroupScheme.IntegralModel.GreenbergMixed
