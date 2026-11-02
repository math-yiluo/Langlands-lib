import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRationalNeighborhoodCover
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartBaseChange
import Langlands.Geometry.Analytic.StrictTestDomain.LocalRationalNeighborhoodStatement
import Langlands.Geometry.Analytic.StrictTestDomain.RationalRepresentationProof

/-! # Strict tests and rational neighborhoods under bounded equivalences -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open Topology CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} (U : Domain K A)
  {P Q : PresentedStrictAffinoidAlgebra K}
  (eA : BoundedAlgEquiv K A P) (eU : BoundedAlgEquiv K U.algebra Q)

/-- The actual strict structural map conjugated through both bounded maps. -/
def strictMap : BoundedAlgHom K P Q :=
  eU.toBoundedAlgHom.comp (U.baseMap.comp eA.symm.toBoundedAlgHom)

/-- The represented subset in the strict ambient spectrum. -/
def strictLocus : Set (BanachSpectrum P) :=
  eA.spectrumHomeomorph ⁻¹' U.locus

theorem strictMap_spectrum (y : BanachSpectrum Q) :
    eA.spectrumHomeomorph
      (BanachSpectrum.comap (strictMap U eA eU).toBoundedRingHom y) =
        U.spectrumMap (eU.spectrumHomeomorph y) := by
  apply BanachSpectrum.ext
  intro a
  change y (eU (U.baseMap (eA.symm (eA a)))) = y (eU (U.baseMap a))
  rw [eA.symm_apply_apply]

/-- Full representation gives all strict-test factorizations after actual
bounded equivalences of the ambient and representing algebras. -/
theorem strictRepresents :
    StrictTestDomain.Represents K (strictMap U eA eU) (strictLocus U eA) := by
  refine ⟨U.represents.1.preimage eA.spectrumHomeomorph.continuous, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro _ ⟨y, rfl⟩
      change eA.spectrumHomeomorph
        (BanachSpectrum.comap (strictMap U eA eU).toBoundedRingHom y) ∈ U.locus
      rw [strictMap_spectrum]
      exact U.represents.hasImageIn _
    · intro x hx
      change eA.spectrumHomeomorph x ∈ U.locus at hx
      obtain ⟨y, hy⟩ := U.represents.2.1.symm ▸ hx
      obtain ⟨z, hz⟩ := eU.spectrumHomeomorph.surjective y
      refine ⟨z, eA.spectrumHomeomorph.injective ?_⟩
      rw [strictMap_spectrum, hz]
      exact hy
  · intro R α hα
    let E := strictEquiv K R
    let α₀ := E.symm.toBoundedAlgHom.comp (α.comp eA.toBoundedAlgHom)
    have hα₀ : HasImageIn K α₀ U.locus :=
      fun x => hα (BanachSpectrum.comap E.symm.toBoundedAlgHom.toBoundedRingHom x)
    obtain ⟨β₀, hβ₀, huniq⟩ := U.represents.2.2 (ofStrict K R) α₀ hα₀
    let β := E.toBoundedAlgHom.comp (β₀.comp eU.symm.toBoundedAlgHom)
    have hβ : β.comp (strictMap U eA eU) = α := by
      apply BoundedAlgHom.ext
      intro p
      change E (β₀ (eU.symm (eU (U.baseMap (eA.symm p))))) = α p
      rw [eU.symm_apply_apply]
      have h := congrArg (fun φ : BoundedAlgHom K A (ofStrict K R) =>
        E (φ (eA.symm p))) hβ₀
      exact h.trans (by
        change E (E.symm (α (eA (eA.symm p)))) = α p
        rw [eA.apply_symm_apply, E.apply_symm_apply])
    refine ⟨β, hβ, ?_⟩
    intro θ hθ
    let θ₀ := E.symm.toBoundedAlgHom.comp (θ.comp eU.toBoundedAlgHom)
    have hθ₀ : θ₀.comp U.baseMap = α₀ := by
      apply BoundedAlgHom.ext
      intro a
      have h := congrArg (fun φ : BoundedAlgHom K P R => φ (eA a)) hθ
      change θ (eU (U.baseMap (eA.symm (eA a)))) = α (eA a) at h
      rw [eA.symm_apply_apply] at h
      exact congrArg E.symm h
    have h := huniq θ₀ hθ₀
    apply BoundedAlgHom.ext
    intro q
    have hb := congrArg (fun φ : BoundedAlgHom K U.algebra (ofStrict K R) =>
      E (φ (eU.symm q))) h
    change E (E.symm (θ (eU (eU.symm q)))) = E (β₀ (eU.symm q)) at hb
    change θ q = E (β₀ (eU.symm q))
    simpa only [eU.apply_symm_apply, E.apply_symm_apply] using hb

/-- The closed strict locus has its actual transported subspace topology. -/
def strictLocusHomeomorph : strictLocus U eA ≃ₜ U.locus :=
  eA.spectrumHomeomorph.sets rfl

variable {U}

/-- Transport strict rational coefficient classes back to the actual generalized
ambient algebra, choosing only weighted-series representatives. -/
def chartOfStrict (d : StrictTestDomain.RationalData K P) : RationalChart K A where
  arity := d.arity
  radii := PositivePolyradius.unit _
  denominator := RationalChart.coefficientRepresentative A (eA.symm d.denominator)
  numerators j := RationalChart.coefficientRepresentative A (eA.symm (d.numerator j))
  generates := by
    change Ideal.span (insert
      (presentationMap K A (RationalChart.coefficientRepresentative A (eA.symm d.denominator)))
      (Set.range fun j => presentationMap K A
        (RationalChart.coefficientRepresentative A (eA.symm (d.numerator j))))) = ⊤
    simp only [RationalChart.presentationMap_coefficientRepresentative]
    have h := congrArg (Ideal.map eA.symm.toBoundedAlgHom.toAlgHom.toRingHom)
      d.generatesUnitIdeal
    simp only [Ideal.map_span,
      Set.image_insert_eq, ← Set.range_comp', Ideal.map_top] at h
    change Ideal.span (insert (eA.symm d.denominator)
      (Set.range fun j => eA.symm (d.numerator j))) = ⊤ at h
    exact h

/-- The transported chart cuts out exactly the inverse-image inequalities. -/
theorem chartOfStrict_locus (d : StrictTestDomain.RationalData K P) :
    (chartOfStrict eA d).locus = eA.spectrumHomeomorph.symm ⁻¹' d.locus := by
  ext x
  change (∀ j : Fin d.arity, x (presentationMap K A
    (RationalChart.coefficientRepresentative A (eA.symm (d.numerator j)))) ≤
      (1 : ℝ) * x (presentationMap K A
        (RationalChart.coefficientRepresentative A (eA.symm d.denominator)))) ↔
    ∀ j, x (eA.symm (d.numerator j)) ≤ x (eA.symm d.denominator)
  simp only [RationalChart.presentationMap_coefficientRepresentative, one_mul]

/-- A strict rational relative neighborhood yields an actual ambient rational
neighborhood of the original full represented domain. -/
def neighborhoodOfStrict (x : U.locus) (d : StrictTestDomain.RationalData K P)
    (hd : d.locus ⊆ strictLocus U eA)
    (hn : d.locus ∈ 𝓝[strictLocus U eA] (eA.spectrumHomeomorph.symm x.val)) :
    RationalNeighborhood U x := by
  let H := strictLocusHomeomorph U eA
  have hs : (chartOfStrict eA d).locus ⊆ U.locus := by
    intro y hy
    rw [chartOfStrict_locus] at hy
    have h := hd hy
    change eA.spectrumHomeomorph (eA.spectrumHomeomorph.symm y) ∈ U.locus at h
    simpa only [Homeomorph.apply_symm_apply] using h
  have hN : (Subtype.val ⁻¹' d.locus : Set (strictLocus U eA)) ∈ 𝓝 (H.symm x) := by
    rw [nhds_subtype_eq_comap_nhdsWithin]
    exact Filter.preimage_mem_comap hn
  refine ⟨chartOfStrict eA d, inclusionOfSubset _ U hs, ?_⟩
  have h := H.symm.continuous.continuousAt.preimage_mem_nhds hN
  convert h using 1
  ext y
  exact Set.ext_iff.mp (chartOfStrict_locus eA d) y.val

include eA eU in
/-- Strict local Gerritzen–Grauert supplies generalized ambient neighborhoods
whenever both algebras have actual strict presentations over the same field. -/
theorem nonempty_rationalNeighborhood_of_strict
    (hGG : StrictTestDomain.LocalRationalNeighborhoodStatement.{u})
    (hK : ∃ a : K, 1 < ‖a‖) (x : U.locus) :
    Nonempty (RationalNeighborhood U x) := by
  let H := strictLocusHomeomorph U eA
  obtain ⟨d, hd, hn⟩ := hGG K hK P Q (strictMap U eA eU) (strictLocus U eA)
    (strictRepresents U eA eU) (H.symm x).val (H.symm x).property
  exact ⟨neighborhoodOfStrict eA x d hd hn⟩

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
