import Langlands.GroupScheme.Reductive.NormalIdempotentDecomposition

/-! # Ring idempotents from the actual clopen group decomposition -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  {ψ : G ⟶ G}

/-- A ring idempotent describing identity and triviality after all affine base changes. -/
structure RingIdempotentDecomposition (ψ : G ⟶ G) where
  element : R
  idempotent : IsIdempotentElem element
  identity_eq : ∀ (C : Type u) [CommRing C] (f : R →+* C), f element = 1 →
    (baseChange (Spec.map (CommRingCat.ofHom f))).map ψ =
      𝟙 ((baseChange (Spec.map (CommRingCat.ofHom f))).obj G)
  zero_eq : ∀ (C : Type u) [CommRing C] (f : R →+* C), f element = 0 →
    (baseChange (Spec.map (CommRingCat.ofHom f))).map ψ = 0

namespace NormalIdempotentDecomposition

variable (D : NormalIdempotentDecomposition ψ)

/-- The idempotent of the affine base with the given clopen identity part. -/
def baseIdempotent : R :=
  Classical.choose (PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen D.clopen)

theorem baseIdempotent_spec : IsIdempotentElem D.baseIdempotent ∧
    (D.identityPart : Set (Spec (CommRingCat.of R))) =
      (PrimeSpectrum.basicOpen D.baseIdempotent : Set (PrimeSpectrum R)) :=
  Classical.choose_spec (PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen D.clopen)

private theorem range_subset_identityPart {C : Type u} [CommRing C] (f : R →+* C)
    (hf : f D.baseIdempotent = 1) :
    Set.range (Spec.map (CommRingCat.ofHom f)) ⊆ Set.range D.identityPart.ι := by
  rintro _ ⟨p, rfl⟩
  have hp : Spec.map (CommRingCat.ofHom f) p ∈ D.identityPart := by
    change Spec.map (CommRingCat.ofHom f) p ∈
      (D.identityPart : Set (Spec (CommRingCat.of R)))
    rw [D.baseIdempotent_spec.2]
    change f D.baseIdempotent ∉ p.asIdeal
    rw [hf]
    exact p.isPrime.one_notMem
  exact ⟨⟨_, hp⟩, rfl⟩

private theorem range_subset_zeroPart {C : Type u} [CommRing C] (f : R →+* C)
    (hf : f D.baseIdempotent = 0) :
    Set.range (Spec.map (CommRingCat.ofHom f)) ⊆ Set.range D.zeroPart.ι := by
  rintro _ ⟨p, rfl⟩
  have hn : Spec.map (CommRingCat.ofHom f) p ∉ D.identityPart := by
    change Spec.map (CommRingCat.ofHom f) p ∉
      (D.identityPart : Set (Spec (CommRingCat.of R)))
    rw [D.baseIdempotent_spec.2]
    change ¬ f D.baseIdempotent ∉ p.asIdeal
    rw [hf]
    exact not_not.mpr p.asIdeal.zero_mem
  have hp : Spec.map (CommRingCat.ofHom f) p ∈ D.identityPart ⊔ D.zeroPart := by
    rw [D.cover]
    trivial
  exact ⟨⟨_, hp.resolve_left hn⟩, rfl⟩

/-- Turn the actual clopen base decomposition into an idempotent with exact
identity/triviality after every ring map where that element is one/zero. -/
def toRingDecomposition : RingIdempotentDecomposition ψ where
  element := D.baseIdempotent
  idempotent := D.baseIdempotent_spec.1
  identity_eq C _ f hf := by
    let q := IsOpenImmersion.lift D.identityPart.ι (Spec.map (CommRingCat.ofHom f))
      (D.range_subset_identityPart f hf)
    exact baseChange_eq_id_of_factor ψ (Spec.map (CommRingCat.ofHom f)) q
      (IsOpenImmersion.lift_fac _ _ _) D.identity_eq
  zero_eq C _ f hf := by
    let q := IsOpenImmersion.lift D.zeroPart.ι (Spec.map (CommRingCat.ofHom f))
      (D.range_subset_zeroPart f hf)
    exact baseChange_eq_zero_of_factor ψ (Spec.map (CommRingCat.ofHom f)) q
      (IsOpenImmersion.lift_fac _ _ _) D.zero_eq

end NormalIdempotentDecomposition
end Langlands.GroupScheme
