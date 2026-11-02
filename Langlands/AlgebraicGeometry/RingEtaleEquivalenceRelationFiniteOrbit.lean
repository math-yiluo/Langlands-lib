import Langlands.AlgebraicGeometry.RingEtaleEquivalenceRelationScheme
import Langlands.AlgebraicGeometry.GroupoidCoactionFiniteAlgebra
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPointTopology
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationClosedIdeal
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Radical ideals of finite closed orbits of affine étale relations -/

universe u

open AlgebraicGeometry Set TopologicalSpace

namespace Langlands.AlgebraicGeometry

namespace FiniteClosedIdeal

variable {B : Type u} [CommRing B]

/-- The spectrum of the quotient by the ideal of a closed discrete subset is
discrete in its actual Zariski topology. -/
lemma discreteTopology_quotient_vanishingIdeal (T : Closeds (PrimeSpectrum B))
    (hd : IsDiscrete (T : Set (PrimeSpectrum B))) :
    DiscreteTopology (PrimeSpectrum
      (B ⧸ PrimeSpectrum.vanishingIdeal (T : Set (PrimeSpectrum B)))) := by
  let I := PrimeSpectrum.vanishingIdeal (T : Set (PrimeSpectrum B))
  have hrange : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = T := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, T.isClosed.closure_eq]
  have hpre : PrimeSpectrum.comap (Ideal.Quotient.mk I) ⁻¹' (T : Set (PrimeSpectrum B)) =
      Set.univ := by
    rw [← hrange, Set.preimage_range]
  have he := PrimeSpectrum.isEmbedding_comap_of_surjective _ _
    (Ideal.Quotient.mk_surjective (I := I))
  have h := hd.preimage he.continuous.continuousOn he.injective
  rw [hpre] at h
  exact isDiscrete_univ_iff.mp h

end FiniteClosedIdeal

namespace RingEtaleEquivalenceRelation

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
  {t : B →+* C}

instance toScheme_isAffine_U (hE : RingEtaleEquivalenceRelation t) :
    IsAffine hE.toScheme.U :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))

instance toScheme_isAffine_R (hE : RingEtaleEquivalenceRelation t) :
    IsAffine hE.toScheme.R :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of C)))

/-- Equality of source and target preimages gives invariance for the actual
point relation of the associated scheme relation. -/
lemma pointInvariant_of_preimage_eq (hE : RingEtaleEquivalenceRelation t)
    {S : Set (PrimeSpectrum B)}
    (hS : PrimeSpectrum.comap (algebraMap B C) ⁻¹' S = PrimeSpectrum.comap t ⁻¹' S) :
    hE.toScheme.PointInvariant S := by
  rintro x y ⟨r, rfl, rfl⟩ hx
  change r ∈ PrimeSpectrum.comap t ⁻¹' S
  rw [← hS]
  exact hx

variable [IsNoetherianRing B]

instance toScheme_isNoetherian_U (hE : RingEtaleEquivalenceRelation t) :
    IsNoetherian hE.toScheme.U :=
  inferInstanceAs (IsNoetherian (Spec (CommRingCat.of B)))

/-- A finite closed orbit chosen inside a nonempty closed invariant subset. -/
noncomputable def finiteClosedOrbit (hE : RingEtaleEquivalenceRelation t)
    (S : Closeds (PrimeSpectrum B)) (hne : (S : Set (PrimeSpectrum B)).Nonempty)
    (hS : PrimeSpectrum.comap (algebraMap B C) ⁻¹' (S : Set (PrimeSpectrum B)) =
      PrimeSpectrum.comap t ⁻¹' (S : Set (PrimeSpectrum B))) :
    Closeds (PrimeSpectrum B) :=
  hE.toScheme.minimalClosedPointInvariant S ⟨hne, hE.pointInvariant_of_preimage_eq hS⟩

lemma finiteClosedOrbit_spec (hE : RingEtaleEquivalenceRelation t)
    (S : Closeds (PrimeSpectrum B)) (hne : (S : Set (PrimeSpectrum B)).Nonempty)
    (hS : PrimeSpectrum.comap (algebraMap B C) ⁻¹' (S : Set (PrimeSpectrum B)) =
      PrimeSpectrum.comap t ⁻¹' (S : Set (PrimeSpectrum B))) :
    let T := hE.finiteClosedOrbit S hne hS
    T ≤ S ∧ (T : Set (PrimeSpectrum B)).Nonempty ∧
      (T : Set (PrimeSpectrum B)).Finite ∧ IsDiscrete (T : Set (PrimeSpectrum B)) ∧
      (∀ p ∈ T, IsClosed ({p} : Set (PrimeSpectrum B))) ∧
      PrimeSpectrum.comap (algebraMap B C) ⁻¹' (T : Set (PrimeSpectrum B)) =
        PrimeSpectrum.comap t ⁻¹' (T : Set (PrimeSpectrum B)) := by
  have hmin := hE.toScheme.minimalClosedPointInvariant_spec S
    ⟨hne, hE.pointInvariant_of_preimage_eq hS⟩
  obtain ⟨hf, hd, hc⟩ := hE.toScheme.finite_discrete_closedPoints_of_minimal _ hmin.2
  exact ⟨hmin.1, hmin.2.1.1, hf, hd, hc,
    hE.toScheme.pointInvariant_preimage_eq hmin.2.1.2⟩

/-- The actual radical ideal defining the chosen finite closed orbit. -/
noncomputable def finiteOrbitIdeal (hE : RingEtaleEquivalenceRelation t)
    (S : Closeds (PrimeSpectrum B)) (hne : (S : Set (PrimeSpectrum B)).Nonempty)
    (hS : PrimeSpectrum.comap (algebraMap B C) ⁻¹' (S : Set (PrimeSpectrum B)) =
      PrimeSpectrum.comap t ⁻¹' (S : Set (PrimeSpectrum B))) : Ideal B :=
  PrimeSpectrum.vanishingIdeal (hE.finiteClosedOrbit S hne hS : Set (PrimeSpectrum B))

lemma finiteOrbitIdeal_spec (hE : RingEtaleEquivalenceRelation t)
    (S : Closeds (PrimeSpectrum B)) (hne : (S : Set (PrimeSpectrum B)).Nonempty)
    (hS : PrimeSpectrum.comap (algebraMap B C) ⁻¹' (S : Set (PrimeSpectrum B)) =
      PrimeSpectrum.comap t ⁻¹' (S : Set (PrimeSpectrum B))) :
    let I := hE.finiteOrbitIdeal S hne hS
    I ≠ ⊤ ∧ I.IsRadical ∧ PrimeSpectrum.zeroLocus (I : Set B) ⊆ S ∧
      I.map (algebraMap B C) = I.map t ∧ DiscreteTopology (PrimeSpectrum (B ⧸ I)) := by
  obtain ⟨hle, hn, hf, hd, hc, hinv⟩ := hE.finiteClosedOrbit_spec S hne hS
  refine ⟨?_, PrimeSpectrum.isRadical_vanishingIdeal _, ?_, ?_, ?_⟩
  · intro htop
    exact hn.ne_empty (PrimeSpectrum.vanishingIdeal_eq_top_iff.mp htop)
  · change PrimeSpectrum.zeroLocus
      (PrimeSpectrum.vanishingIdeal
        (hE.finiteClosedOrbit S hne hS : Set (PrimeSpectrum B)) : Set B) ⊆ _
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      (hE.finiteClosedOrbit S hne hS).isClosed.closure_eq]
    exact hle
  · exact FiniteClosedIdeal.map_vanishingIdeal_eq_of_preimage_eq
      (algebraMap B C) t hE.etale_algebraMap hE.etale_t hf hc hinv
  · exact FiniteClosedIdeal.discreteTopology_quotient_vanishingIdeal _ hd

/-- The chosen orbit quotient is a nonzero reduced Artinian ring. -/
lemma finiteOrbitIdeal_quotient (hE : RingEtaleEquivalenceRelation t)
    (S : Closeds (PrimeSpectrum B)) (hne : (S : Set (PrimeSpectrum B)).Nonempty)
    (hS : PrimeSpectrum.comap (algebraMap B C) ⁻¹' (S : Set (PrimeSpectrum B)) =
      PrimeSpectrum.comap t ⁻¹' (S : Set (PrimeSpectrum B))) :
    let I := hE.finiteOrbitIdeal S hne hS
    Nontrivial (B ⧸ I) ∧ IsReduced (B ⧸ I) ∧ IsArtinianRing (B ⧸ I) := by
  obtain ⟨hneI, hrad, _, _, hd⟩ := hE.finiteOrbitIdeal_spec S hne hS
  let := hd
  exact ⟨Ideal.Quotient.nontrivial_iff.mpr hneI,
    (Ideal.isRadical_iff_quotient_reduced _).mp hrad,
    GroupoidCoactionFiniteAlgebra.isArtinianRing_of_discrete _⟩

end RingEtaleEquivalenceRelation

end Langlands.AlgebraicGeometry
