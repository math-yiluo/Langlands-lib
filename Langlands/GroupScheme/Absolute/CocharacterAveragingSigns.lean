import Langlands.GroupScheme.Absolute.CocharacterDescentLattice

/-! # Three-sign preservation under integral Galois averaging -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.CocharacterAveraging

section PairingSigns

variable {R : Type u} [CommRing R] [IsDomain R]
  (T : CommGroupScheme (Spec (CommRingCat.of R)))
  (Φ : Set (characterLattice T))

/-- Two actual cocharacters have the same pairing signs on a character family
when their nonnegative, zero, and strictly positive pairings agree there. -/
def HaveSamePairingSigns (ν μ : cocharacterLattice T) : Prop :=
  ∀ χ ∈ Φ,
    (0 ≤ latticePairing T χ ν ↔ 0 ≤ latticePairing T χ μ) ∧
    (latticePairing T χ ν = 0 ↔ latticePairing T χ μ = 0) ∧
    (0 < latticePairing T χ ν ↔ 0 < latticePairing T χ μ)

theorem HaveSamePairingSigns.refl (ν : cocharacterLattice T) :
    HaveSamePairingSigns T Φ ν ν :=
  fun _ _ => ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem HaveSamePairingSigns.symm {ν μ : cocharacterLattice T}
    (h : HaveSamePairingSigns T Φ ν μ) : HaveSamePairingSigns T Φ μ ν :=
  fun χ hχ => ⟨(h χ hχ).1.symm, (h χ hχ).2.1.symm, (h χ hχ).2.2.symm⟩

theorem HaveSamePairingSigns.trans {ν μ η : cocharacterLattice T}
    (h₁ : HaveSamePairingSigns T Φ ν μ) (h₂ : HaveSamePairingSigns T Φ μ η) :
    HaveSamePairingSigns T Φ ν η :=
  fun χ hχ => ⟨(h₁ χ hχ).1.trans (h₂ χ hχ).1,
    (h₁ χ hχ).2.1.trans (h₂ χ hχ).2.1, (h₁ χ hχ).2.2.trans (h₂ χ hχ).2.2⟩

end PairingSigns

section OrbitSum

variable (k K : Type u) [CommRing k] [CommRing K] [IsDomain K] [Algebra k K]
  [Fintype (K ≃ₐ[k] K)] (T : CommGroupScheme (Spec (CommRingCat.of k)))
  (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
  (Φ : Set (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)))
  (hΦ : ∀ (σ : K ≃ₐ[k] K) χ,
    characterLattice.galoisRepresentation k K T σ χ ∈ Φ ↔ χ ∈ Φ)
  (hcone : ∀ (σ : K ≃ₐ[k] K) χ,
    (characterLattice.galoisRepresentation k K T σ χ ∈ Φ ∧
      0 ≤ latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        (characterLattice.galoisRepresentation k K T σ χ) ν) ↔
    (χ ∈ Φ ∧ 0 ≤ latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      χ ν))
  (hneg : ∀ χ ∈ Φ, -χ ∈ Φ)

include hΦ hcone hneg in
/-- On a negation-closed character family, stable nonnegative signs also preserve
zero and strictly positive signs under the integral Galois orbit sum. -/
theorem galoisOrbitSum_signs_iff :
    HaveSamePairingSigns ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      Φ (galoisOrbitSum k K T ν) ν := by
  intro χ hχ
  have hp := galoisOrbitSum_nonneg_iff k K T ν Φ hΦ hcone χ hχ
  have hn := galoisOrbitSum_nonneg_iff k K T ν Φ hΦ hcone (-χ) (hneg χ hχ)
  simp only [map_neg, LinearMap.neg_apply, neg_nonneg] at hn
  refine ⟨hp, ⟨?_, ?_⟩, ?_⟩
  · intro h
    exact le_antisymm (hn.mp (le_of_eq h)) (hp.mp (le_of_eq h.symm))
  · intro h
    exact le_antisymm (hn.mpr (le_of_eq h)) (hp.mpr (le_of_eq h.symm))
  · simpa only [not_le] using not_congr hn

end OrbitSum

section Descent

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffineHom T.X.hom]
  (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))

/-- The descended integral orbit sum preserves all three signs on a
negation-closed character family with a stable nonnegative subset. -/
theorem descendedOrbitSum_signs_iff
    (Φ : Set (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)))
    (hΦ : ∀ (σ : K ≃ₐ[k] K) χ,
      characterLattice.galoisRepresentation k K T σ χ ∈ Φ ↔ χ ∈ Φ)
    (hcone : ∀ (σ : K ≃ₐ[k] K) χ,
      (characterLattice.galoisRepresentation k K T σ χ ∈ Φ ∧
        0 ≤ latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
          (characterLattice.galoisRepresentation k K T σ χ) ν) ↔
      (χ ∈ Φ ∧ 0 ≤ latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        χ ν))
    (hneg : ∀ χ ∈ Φ, -χ ∈ Φ) :
    HaveSamePairingSigns ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) Φ
      (cocharacterLattice.baseChange (algebraBaseMap k K) T (descendedOrbitSum k K T ν)) ν := by
  rw [baseChange_descendedOrbitSum]
  exact galoisOrbitSum_signs_iff k K T ν Φ hΦ hcone hneg

end Descent

end Langlands.GroupScheme.CocharacterAveraging
