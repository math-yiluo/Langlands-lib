import Langlands.GroupScheme.Absolute.CocharacterAveragingSigns

/-! # Descent of a Galois-stable pairing-sign class -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.CocharacterAveraging

section OrbitSigns

variable (k K : Type u) [CommRing k] [CommRing K] [IsDomain K] [Algebra k K]
  [Fintype (K ≃ₐ[k] K)] (T : CommGroupScheme (Spec (CommRingCat.of k)))
  (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
  (Φ : Set (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)))

/-- If every translate has the original signs on a fixed character family, so
does the integral orbit sum; the family needs no closure or stability premise. -/
theorem galoisOrbitSum_signs_of_orbit_signs
    (horbit : ∀ σ : K ≃ₐ[k] K,
      HaveSamePairingSigns ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) Φ
        (cocharacterLattice.galoisRepresentation k K T σ ν) ν) :
    HaveSamePairingSigns ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) Φ
      (galoisOrbitSum k K T ν) ν := by
  intro χ hχ
  let f := (latticePairing
    ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) χ).toAddMonoidHom
  have hp := nonneg_orbitSum_iff
    (cocharacterLattice.galoisRepresentation k K T) ν f
    (fun σ => (horbit σ χ hχ).1)
  have hn := nonneg_orbitSum_iff
    (cocharacterLattice.galoisRepresentation k K T) ν (-f) (fun σ => by
      simpa only [f, AddMonoidHom.neg_apply, LinearMap.toAddMonoidHom_coe,
        neg_nonneg, not_lt] using
        not_congr ((horbit σ χ hχ).2.2))
  change (0 ≤ latticePairing
    ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) χ
      (galoisOrbitSum k K T ν) ↔
    0 ≤ latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) χ ν) at hp
  change (0 ≤ -latticePairing
    ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) χ
      (galoisOrbitSum k K T ν) ↔
    0 ≤ -latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) χ ν) at hn
  simp only [neg_nonneg] at hn
  refine ⟨hp, ⟨?_, ?_⟩, ?_⟩
  · intro h
    exact le_antisymm (hn.mp (le_of_eq h)) (hp.mp (le_of_eq h.symm))
  · intro h
    exact le_antisymm (hn.mpr (le_of_eq h)) (hp.mpr (le_of_eq h.symm))
  · simpa only [not_le] using not_congr hn

end OrbitSigns

section Descent

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffineHom T.X.hom]
  (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
  (Φ : Set (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)))
  (horbit : ∀ σ : K ≃ₐ[k] K,
    HaveSamePairingSigns ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) Φ
      (cocharacterLattice.galoisRepresentation k K T σ ν) ν)

include horbit in
/-- Exact recovery of the descended orbit sum gives a representative of the
original pairing-sign class after base change. -/
theorem descendedOrbitSum_signs_of_orbit_signs :
    HaveSamePairingSigns ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) Φ
      (cocharacterLattice.baseChange (algebraBaseMap k K) T (descendedOrbitSum k K T ν)) ν := by
  rw [baseChange_descendedOrbitSum]
  exact galoisOrbitSum_signs_of_orbit_signs k K T ν Φ horbit

/-- An actual cocharacter over the original field whose base change has the
prescribed signs, obtained by descending the integral orbit sum. -/
def descendedSignRepresentative :
    {μ : cocharacterLattice T //
      HaveSamePairingSigns ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) Φ
        (cocharacterLattice.baseChange (algebraBaseMap k K) T μ) ν} :=
  ⟨descendedOrbitSum k K T ν,
    descendedOrbitSum_signs_of_orbit_signs k K T ν Φ horbit⟩

end Descent

end Langlands.GroupScheme.CocharacterAveraging
