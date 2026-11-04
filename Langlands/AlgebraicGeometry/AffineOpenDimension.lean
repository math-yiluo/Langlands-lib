import Langlands.AlgebraicGeometry.FiniteTypeDomainDimension
import Langlands.AlgebraicGeometry.SchemePureDimensionAffine

/-! # Dimension on nonempty opens of finite-type domain spectra -/

universe u v

open Set Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- The actual spectrum of a principal localization is the corresponding basic open. -/
noncomputable def localizationAwayBasicOpenHomeomorph
    {A : Type v} [CommRing A] (s : A) :
    PrimeSpectrum (Localization.Away s) ≃ₜ PrimeSpectrum.basicOpen s :=
  (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away s) s).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (PrimeSpectrum.localization_away_comap_range (Localization.Away s) s))

/-- A nonempty basic open of a finite-type domain spectrum retains its dimension. -/
theorem topologicalKrullDim_basicOpen_of_finiteType_domain
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (s : A) (hs : s ≠ 0) :
    topologicalKrullDim (PrimeSpectrum.basicOpen s) = ringKrullDim A := by
  rw [← (localizationAwayBasicOpenHomeomorph s).isHomeomorph.topologicalKrullDim_eq _,
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_away_eq_of_finiteType_domain k A s hs

/-- Every nonempty open of a finite-type domain spectrum has the same dimension. -/
theorem topologicalKrullDim_open_of_finiteType_domain
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (U : Opens (PrimeSpectrum A)) (hne : (U : Set (PrimeSpectrum A)).Nonempty) :
    topologicalKrullDim U = ringKrullDim A := by
  apply le_antisymm
  · exact (topologicalKrullDim_subspace_le (PrimeSpectrum A) U).trans_eq
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A)
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨_, ⟨s, rfl⟩, hxs, hsU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp U.isOpen x hx
    have hs : s ≠ 0 := fun h => hxs (h ▸ x.asIdeal.zero_mem)
    rw [← topologicalKrullDim_basicOpen_of_finiteType_domain k A s hs]
    exact (Topology.IsEmbedding.inclusion hsU).isInducing.topologicalKrullDim_le

/-- Every nonempty open in the zero locus of a prime of a finite-type algebra
has the dimension of the actual prime quotient. -/
theorem topologicalKrullDim_open_primeZeroLocus
    (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A]
    (p : Ideal A) [p.IsPrime]
    (U : Opens (PrimeSpectrum.zeroLocus (p : Set A)))
    (hne : (U : Set (PrimeSpectrum.zeroLocus (p : Set A))).Nonempty) :
    topologicalKrullDim U = ringKrullDim (A ⧸ p) := by
  let e := quotientSpectrumZeroLocusHomeomorph p
  let V : Opens (PrimeSpectrum (A ⧸ p)) := ⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩
  have hV : (V : Set (PrimeSpectrum (A ⧸ p))).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨e.symm x, by simpa [V] using hx⟩
  let eU : V ≃ₜ U := e.subtype (fun _ => Iff.rfl)
  exact (eU.isHomeomorph.topologicalKrullDim_eq _).symm.trans
    (topologicalKrullDim_open_of_finiteType_domain k (A ⧸ p) V hV)

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
