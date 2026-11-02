import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeLaurentBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCancellation
import Langlands.Geometry.Analytic.Spectrum.Properties

/-! # Full domain representations in actual relative Laurent annuli -/

noncomputable section

universe u

namespace Langlands.Analytic.RelativeLaurentAnnulus

open PresentedAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (t : ℝ) [Fact (0 < t)] {A B : PresentedAffinoidAlgebra K}

/-- The structural spectrum square of actual annulus transport commutes. -/
theorem restriction_comap_transport (φ : BoundedAlgHom K A B)
    (y : BanachSpectrum (algebra K B t)) :
    restriction K A t (BanachSpectrum.comap (transport K t φ).toBoundedRingHom y) =
      BanachSpectrum.comap φ.toBoundedRingHom (restriction K B t y) := by
  apply BanachSpectrum.ext
  intro a
  exact congrArg (fun b : algebra K B t => y b) (transport_baseMap K t φ a)

/-- The actual spectral image of the transported domain structural map. -/
def liftedLocus (U : Domain K A) : Set (BanachSpectrum (algebra K A t)) :=
  Set.range (BanachSpectrum.comap (transport K t U.baseMap).toBoundedRingHom)

/-- Every point of the actual lifted image restricts into the original domain. -/
theorem liftedLocus_subset_preimage (U : Domain K A) :
    liftedLocus K t U ⊆ restriction K A t ⁻¹' U.locus := by
  rintro _ ⟨y, rfl⟩
  change restriction K A t
    (BanachSpectrum.comap (transport K t U.baseMap).toBoundedRingHom y) ∈ U.locus
  rw [restriction_comap_transport]
  exact U.represents.hasImageIn _

/-- The Gauss section detects exactly the original represented domain locus. -/
theorem preimage_gaussSection_liftedLocus (U : Domain K A) :
    gaussSection K A t ⁻¹' liftedLocus K t U = U.locus := by
  ext x
  constructor
  · intro hx
    have h := liftedLocus_subset_preimage K t U hx
    change restriction K A t (gaussSection K A t x) ∈ U.locus at h
    simpa only [restriction_gaussSection] using h
  · intro hx
    obtain ⟨y, hy⟩ := U.represents.2.1.symm ▸ hx
    refine ⟨sectionPoint K U.algebra t y, ?_⟩
    exact (comap_transport_sectionPoint K t U.baseMap y).trans
      (congrArg (sectionPoint K A t) hy)

/-- Restriction of the actual lifted image is exactly the original domain locus. -/
theorem image_restriction_liftedLocus (U : Domain K A) :
    restriction K A t '' liftedLocus K t U = U.locus := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact liftedLocus_subset_preimage K t U hz
  · intro x hx
    refine ⟨gaussSection K A t x, ?_, restriction_gaussSection K A t x⟩
    exact (Set.ext_iff.mp (preimage_gaussSection_liftedLocus K t U) x).mpr hx

/-- Bounded annulus pushout lifts the full affinoid-test representation property. -/
theorem represents_transport (U : Domain K A) :
    Represents K (transport K t U.baseMap) (liftedLocus K t U) := by
  refine ⟨(isCompact_range (BanachSpectrum.comapContinuous
    (transport K t U.baseMap).toBoundedRingHom).continuous).isClosed, rfl, ?_⟩
  intro R α hα
  have hα' : HasImageIn K (α.comp (baseMap K A t)) U.locus := by
    intro x
    exact liftedLocus_subset_preimage K t U (hα x)
  obtain ⟨β, hβ, _⟩ := U.represents.2.2 R (α.comp (baseMap K A t)) hα'
  refine ⟨pushoutLift K t R α β,
    pushoutLift_comp_transport K t R U.baseMap α β hβ.symm, ?_⟩
  intro θ hθ
  apply pushout_hom_ext K t U.baseMap θ (pushoutLift K t R α β)
  · exact hθ.trans (pushoutLift_comp_transport K t R U.baseMap α β hβ.symm).symm
  · rw [pushoutLift_comp_baseMap]
    apply U.represents.hom_ext R
    calc
      (θ.comp (baseMap K U.algebra t)).comp U.baseMap =
          θ.comp ((transport K t U.baseMap).comp (baseMap K A t)) := by
        rw [transport_comp_baseMap]
        rfl
      _ = α.comp (baseMap K A t) := by
        rw [← BoundedAlgHom.comp_assoc, hθ]
      _ = β.comp U.baseMap := hβ.symm

/-- The actual annulus extension of a full represented affinoid domain. -/
def liftedDomain (U : Domain K A) : Domain K (algebra K A t) where
  algebra := algebra K U.algebra t
  baseMap := transport K t U.baseMap
  locus := liftedLocus K t U
  represents := represents_transport K t U

@[simp] theorem liftedDomain_algebra (U : Domain K A) :
    (liftedDomain K t U).algebra = algebra K U.algebra t := rfl

@[simp] theorem liftedDomain_baseMap (U : Domain K A) :
    (liftedDomain K t U).baseMap = transport K t U.baseMap := rfl

@[simp] theorem liftedDomain_locus (U : Domain K A) :
    (liftedDomain K t U).locus = liftedLocus K t U := rfl

/-- The continuous Gauss section pulls the actual lifted domain back to its source locus. -/
theorem preimage_gaussSection_liftedDomain (U : Domain K A) :
    gaussSection K A t ⁻¹' (liftedDomain K t U).locus = U.locus :=
  preimage_gaussSection_liftedLocus K t U

end Langlands.Analytic.RelativeLaurentAnnulus
