import Langlands.CommutativeAlgebra.FormallySmoothLocalCompletion
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Noetherian finiteness inputs for generated images -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.ImageGeneration

/-- An antitone sequence of prime ideals of a Noetherian ring is eventually constant. -/
theorem exists_forall_eq_of_antitone_isPrime {A : Type*} [CommRing A] [IsNoetherianRing A]
    (p : ℕ → Ideal A) (hp : Antitone p) (hprime : ∀ n, (p n).IsPrime) :
    ∃ N, ∀ m, N ≤ m → p m = p N := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ m, (p N).height ≤ (p m).height := by
    obtain ⟨_, ⟨N, rfl⟩, hmin⟩ :=
      WellFounded.has_min wellFounded_lt (Set.range fun n => (p n).height) ⟨_, 0, rfl⟩
    exact ⟨N, fun m => not_lt.1 (hmin _ ⟨m, rfl⟩)⟩
  refine ⟨N, fun m hm => ?_⟩
  have := hprime m
  exact Ideal.eq_of_le_of_height_le (I := p m) (hp hm) (hN m)

/-- A closed immersion from a Noetherian affine scheme to itself is an isomorphism. -/
theorem isIso_of_isClosedImmersion_endo {X : Scheme.{u}} [IsAffine X] [IsLocallyNoetherian X]
    (φ : X ⟶ X) [IsClosedImmersion φ] : IsIso φ := by
  have : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  exact IsClosedImmersion.isIso_of_injective_of_isAffine
    (Langlands.CommutativeAlgebra.FormallySmoothLocalCompletion.injective_of_surjective_endo φ.appTop.hom
      (IsClosedImmersion.isAffine_surjective_of_isAffine φ).2)

end Langlands.GroupScheme.ImageGeneration
