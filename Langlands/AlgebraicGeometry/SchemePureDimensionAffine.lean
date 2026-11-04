import Langlands.AlgebraicGeometry.SchemeFiberGeometry
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! # Pure dimension of affine schemes and their component quotient rings -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Each minimal-prime quotient of an actual commutative ring has dimension `d`. -/
def HasPureRingDimension (A : Type u) [CommRing A] (d : ℕ) : Prop :=
  ∀ p : Ideal A, p ∈ minimalPrimes A → ringKrullDim (A ⧸ p) = (d : WithBot ℕ∞)

variable {A : Type u} [CommRing A] {d : ℕ}

/-- The spectrum of a quotient is the zero locus of its ideal, with the subspace topology. -/
noncomputable def quotientSpectrumZeroLocusHomeomorph (I : Ideal A) :
    PrimeSpectrum (A ⧸ I) ≃ₜ PrimeSpectrum.zeroLocus (I : Set A) :=
  (PrimeSpectrum.isClosedEmbedding_comap_of_surjective (A ⧸ I) (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (by
        rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
          Ideal.mk_ker]))

/-- A closed component's topological dimension is the dimension of its quotient ring. -/
theorem topologicalKrullDim_zeroLocus (I : Ideal A) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set A)) = ringKrullDim (A ⧸ I) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (quotientSpectrumZeroLocusHomeomorph I).isHomeomorph.topologicalKrullDim_eq _ |>.symm

/-- Exact componentwise comparison, valid for every commutative ring. -/
theorem hasPureDimension_spec_iff :
    HasPureDimension (Spec (CommRingCat.of A)) d ↔ HasPureRingDimension A d := by
  constructor
  · intro h p hp
    have hcomp : PrimeSpectrum.zeroLocus (p : Set A) ∈
        irreducibleComponents (PrimeSpectrum A) := by
      rw [PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents, hp.1.1.isRadical.radical]
      exact hp
    rw [← topologicalKrullDim_zeroLocus]
    exact h _ hcomp
  · intro h Z hZ
    change Z ∈ irreducibleComponents (PrimeSpectrum A) at hZ
    rw [← PrimeSpectrum.zeroLocus_minimalPrimes A] at hZ
    obtain ⟨p, hp, rfl⟩ := hZ
    change topologicalKrullDim (PrimeSpectrum.zeroLocus (p : Set A)) = _
    rw [topologicalKrullDim_zeroLocus]
    exact h p hp

/-- On any affine scheme the same condition is computed by its actual global sections. -/
theorem hasPureDimension_iff_globalSections (X : Scheme.{u}) [IsAffine X] :
    HasPureDimension X d ↔ HasPureRingDimension Γ(X, ⊤) d :=
  (hasPureDimension_iff_of_iso X.isoSpec).trans hasPureDimension_spec_iff

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
