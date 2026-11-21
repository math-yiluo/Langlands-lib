import Langlands.HarmonicAnalysis.Distribution.NormalizedProductChartDescent
import Langlands.HarmonicAnalysis.Distribution.RealSpectralCoefficientDescent
import Langlands.HarmonicAnalysis.Distribution.RealSpectralSupportDescent

/-! # Transpose-odd vanishing on the full real matrix space -/

noncomputable section

open Filter Set TopologicalSpace
open scoped ContDiff Distributions Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4

namespace Langlands.HarmonicAnalysis

section Box

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}

/-- A symmetric open coordinate box transported to a real normed space. -/
def centeredCoordinateTestBox (b : (Fin d → ℝ) ≃L[ℝ] E) (r : ℝ) : Opens E :=
  ⟨b.symm ⁻¹' (openIntervalBox d (-r) r : Set (Fin d → ℝ)),
    (openIntervalBox d (-r) r).isOpen.preimage b.symm.continuous⟩

theorem preimage_centeredCoordinateTestBox (b : (Fin d → ℝ) ≃L[ℝ] E) (r : ℝ) :
    b ⁻¹' (centeredCoordinateTestBox b r : Set E) =
      (openIntervalBox d (-r) r : Set (Fin d → ℝ)) := by
  ext x
  change b.symm (b x) ∈ openIntervalBox d (-r) r ↔ x ∈ openIntervalBox d (-r) r
  rw [b.symm_apply_apply]

theorem zero_mem_centeredCoordinateTestBox (b : (Fin d → ℝ) ≃L[ℝ] E) {r : ℝ} (hr : 0 < r) :
    0 ∈ centeredCoordinateTestBox b r := by
  change b.symm 0 ∈ openIntervalBox d (-r) r
  rw [map_zero, mem_openIntervalBox]
  exact fun _ => ⟨neg_lt_zero.mpr hr, hr⟩

/-- Centered coordinate boxes give arbitrarily small neighborhoods of zero. -/
theorem exists_centeredCoordinateTestBox_le (b : (Fin d → ℝ) ≃L[ℝ] E) {O : Opens E}
    (hO : 0 ∈ O) : ∃ r : ℝ, 0 < r ∧ centeredCoordinateTestBox b r ≤ O := by
  have hpre : b ⁻¹' (O : Set E) ∈ 𝓝 (0 : Fin d → ℝ) :=
    b.continuous.continuousAt.preimage_mem_nhds (by simpa using O.isOpen.mem_nhds hO)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨r, hr, fun x hx => ?_⟩
  have hbx : b.symm x ∈ openIntervalBox d (-r) r := hx
  have hb : b.symm x ∈ Metric.ball 0 r := by
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hr]
    intro i
    rw [Real.norm_eq_abs, abs_lt]
    exact (mem_openIntervalBox.mp hbx) i
  have h := hsub hb
  change b (b.symm x) ∈ O at h
  rwa [b.apply_symm_apply] at h

end Box

namespace RealGeneralLinearDistribution

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation:max "T[" A "]" => LinearMap.range (matrixConjugationTangent A)
local notation:max "Z[" A "]" => realMatrixSemisimpleDirections A

private theorem exists_spectralSliceOpen (A : Mat) {R : Set (Mat × Mat)} (hR : IsOpen R)
    (hR₀ : (A, A) ∈ R) {O : Opens Z[A]} (hO : 0 ∈ O) :
    ∃ U : Opens Z[A], 0 ∈ U ∧ U ≤ O ∧
      (∀ z ∈ U, (A + (z : Mat), A + (z : Mat)) ∈ R) ∧
      ∀ z ∈ U, T[A + (z : Mat)] = T[A] := by
  have hc : Continuous (fun z : Z[A] => A + (z : Mat)) :=
    continuous_const.add continuous_subtype_val
  have hdiag : ∀ᶠ z : Z[A] in 𝓝 0, (A + (z : Mat), A + (z : Mat)) ∈ R :=
    (hc.prodMk hc).continuousAt.preimage_mem_nhds (by simpa using hR.mem_nhds hR₀)
  have hcoe : Tendsto (fun z : Z[A] => (z : Mat)) (𝓝 0) (𝓝 (0 : Mat)) :=
    continuous_subtype_val.tendsto (0 : Z[A])
  have ht : ∀ᶠ z : Z[A] in 𝓝 0, T[A + (z : Mat)] = T[A] :=
    (hcoe.eventually (eventually_range_matrixConjugationTangent_add_semisimpleDirection_eq A)).mono
      fun z hz => hz z.property
  have hnear : ∀ᶠ z : Z[A] in 𝓝 0,
      z ∈ O ∧ (A + (z : Mat), A + (z : Mat)) ∈ R ∧ T[A + (z : Mat)] = T[A] := by
    filter_upwards [O.isOpen.mem_nhds hO, hdiag, ht] with z hz hzdiag hzt
    exact ⟨hz, hzdiag, hzt⟩
  obtain ⟨U, ⟨h₀, hU⟩, hsub⟩ := (nhds_basis_opens (0 : Z[A])).mem_iff.mp hnear
  exact ⟨⟨U, hU⟩, h₀, fun _ hz => (hsub hz).1, fun _ hz => (hsub hz).2.1,
    fun _ hz => (hsub hz).2.2⟩

set_option maxHeartbeats 3000000 in
private theorem exists_spectralVanishingNeighborhood (D : FullDistribution n)
    (hconj : IsFullConjugationInvariant D) (hodd : IsFullTransposeAntiInvariant D) (A : Mat)
    (hA : Distribution.IsVanishingOn D (realMatrixSpectralStrictSuperlevel A)) :
    ∃ O : Opens Mat, A ∈ O ∧ Distribution.IsVanishingOn D (O : Set Mat) := by
  obtain ⟨W, N, J, e, R, hZW, hTW, hN, _, hformula, h₀, heA, hunit,
    he, hei, hR, hR₀, hrec, hfixed⟩ := exists_realSpectralStratumChart A
  let L : ((T[A] × Z[A]) × N) ≃L[ℝ] Mat :=
    LinearEquiv.toContinuousLinearEquiv (𝕜 := ℝ) (E := (↥T[A] × ↥Z[A]) × ↥N) (F := Mat)
      (realMatrixStratumLinearEquiv hZW hTW hN)
  have hsource : ((0 : T[A] × Z[A]), (0 : N)) ∈ e.source := h₀
  have he₀ : e ((0 : T[A] × Z[A]), (0 : N)) = A := heA
  obtain ⟨U₁, V₁, hU₁, hV₁, _, hsub, hhigh⟩ :=
    exists_realSpectralChart_product e hsource he₀ hfixed (s := univ) Filter.univ_mem
  have hUV : productTestDomain (E := ↥T[A] × ↥Z[A]) (W := ↥N) U₁ V₁ ≤
      chartSource (E := (↥T[A] × ↥Z[A]) × ↥N) (F := Mat) e :=
    hsub
  have hzero := isVanishingOn_normalizedProductChartDistribution he hei L hUV D hA hhigh
  have hp₁ : ((0 : T[A] × Z[A]), (0 : N)) ∈ productTestDomain U₁ V₁ := ⟨hU₁, hV₁⟩
  obtain ⟨U₂, V₂, K, hp₂, hK₂, hK⟩ := exists_productTestDomain_subset_compact hp₁
  have hnear : (U₂ : Set (T[A] × Z[A])) ∈ 𝓝 ((0 : T[A]), (0 : Z[A])) :=
    U₂.isOpen.mem_nhds (mem_productTestDomain.mp hp₂).1
  obtain ⟨Ot, Oz, htOpen, ht₀, hzOpen, hz₀, hprod⟩ := mem_nhds_prod_iff'.mp hnear
  obtain ⟨U, hU₀, hUz, hdiag, hTangent⟩ :=
    exists_spectralSliceOpen A hR hR₀ (O := ⟨Oz, hzOpen⟩) hz₀
  let b : (Fin (Module.finrank ℝ T[A]) → ℝ) ≃L[ℝ] T[A] :=
    LinearEquiv.toContinuousLinearEquiv (𝕜 := ℝ) (F := ↥T[A])
      (Module.finBasis ℝ T[A]).equivFun.symm
  obtain ⟨r, hr, hQt⟩ := exists_centeredCoordinateTestBox_le b (O := ⟨Ot, htOpen⟩) ht₀
  let Q := centeredCoordinateTestBox b r
  have hQ : (0 : T[A]) ∈ Q := zero_mem_centeredCoordinateTestBox b hr
  have hV : (0 : N) ∈ V₂ := (mem_productTestDomain.mp hp₂).2
  have hQU : productTestDomain Q U ≤ U₂ := fun _ hz => hprod ⟨hQt hz.1, hUz hz.2⟩
  have hK₀ : (productTestDomain (productTestDomain Q U) V₂ : Set ((T[A] × Z[A]) × N)) ⊆ K :=
    fun _ hp => hK₂ ⟨hQU hp.1, hp.2⟩
  have hΩ : productTestDomain (productTestDomain Q U) V₂ ≤ chartSource e :=
    (hK₀.trans hK).trans hUV
  have hord := hasTransverseJetOrder_normalizedProductChartDistribution he hei L hUV D hzero hK hK₀
  have hvan : normalizedProductChartDistribution he hei L hΩ D = 0 :=
    normalizedProductChartDistribution_eq_zero_of_realSpectralChart J he hei hformula hunit L hΩ D
      hconj hZW hTW hN hR hrec hdiag hTangent hQ hV hodd b
      ((neg_lt_zero.mpr hr).trans hr) (preimage_centeredCoordinateTestBox b r) _ hord
  have hp : (0 : (T[A] × Z[A]) × N) ∈ productTestDomain (productTestDomain Q U) V₂ :=
    ⟨⟨hQ, hU₀⟩, hV⟩
  obtain ⟨O, hO, hDO⟩ := exists_vanishingNeighborhood_of_productChart_eq_zero e he hei hp hΩ D
    (restrictProductChartDistribution_eq_zero_of_normalized he hei L hΩ D hvan)
  exact ⟨O, heA ▸ hO, hDO⟩

/-- Every conjugation-invariant and transpose-odd distribution on all real
square matrices is zero. -/
theorem fullMatrixDistribution_eq_zero_of_conjugationInvariant_transposeAntiInvariant
    (D : FullDistribution n) (hconj : IsFullConjugationInvariant D)
    (hodd : IsFullTransposeAntiInvariant D) : D = 0 :=
  realMatrixDistribution_eq_zero_of_spectralDescent D (exists_spectralVanishingNeighborhood D hconj hodd)

/-- Every conjugation-invariant distribution on the full real matrix space is
invariant under transpose. -/
theorem isFullTransposeInvariant_of_isFullConjugationInvariant
    (D : FullDistribution n) (hD : IsFullConjugationInvariant D) :
    IsFullTransposeInvariant D :=
  isFullTransposeInvariant_of_antiInvariant_eq_zero
    fullMatrixDistribution_eq_zero_of_conjugationInvariant_transposeAntiInvariant D hD

end RealGeneralLinearDistribution
end Langlands.HarmonicAnalysis
