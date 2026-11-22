import Langlands.Global.AdelicWeightedPointwiseConvolution
import Langlands.Global.LeftCosetLocalMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Local integrability from a weighted chamber norm -/

noncomputable section
set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory Filter MeasureTheory Set Topology
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global.WeightedSiegel

open AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

local notation "A" => AdelicGroupPoints F G
local notation "μG" => (Measure.haar : Measure A)

/-- A finite weighted chamber integral gives local Haar integrability of an automorphic
representative when the open chamber covers the rational quotient. -/
def WeightedChamberLocalIntegrabilityStatement : Prop :=
  ∀ (ell : RealCharacterDual F P → ℝ), Continuous ell →
  ∀ (S : Set (RealCharacterDual F P)), IsOpen S →
  (∀ x : A, ∃ r : rationalSubgroup F G, hK.height ((r : A) * x) ∈ S) →
  ∀ (f : A → ℂ), Measurable f →
  (∀ (r : rationalSubgroup F G) x, f ((r : A) * x) = f x) →
  (∫⁻ g in LeftCosetSpace.fundamentalDomain (parabolicPrincipalSubgroup F p)
      (isDiscrete_parabolicPrincipalSubgroup F p),
      ‖f g‖ₑ ^ (2 : ℕ) * chamberDensity F p hK ell S g ∂μG) < ∞ →
  LocallyIntegrable f μG

theorem weightedChamberLocalIntegrability : WeightedChamberLocalIntegrabilityStatement hK := by
  intro ell hell S hS hcover f hf hfinv hfin
  let : MeasurableSpace (RealCharacterDual F P) := borel _
  let : BorelSpace (RealCharacterDual F P) := ⟨rfl⟩
  let Γ := parabolicPrincipalSubgroup F p
  let hΓ := isDiscrete_parabolicPrincipalSubgroup F p
  let q := LeftCosetSpace.mk Γ
  let T := domainHeight F p hK ⁻¹' S
  let δ := domainDensity F p hK ell
  let fQ : DomainQuotient F p → ℂ := LeftCosetSpace.lift Γ f
    (fun dlt x => hfinv ⟨dlt.val, parabolicPrincipalSubgroup_le F p dlt.property⟩ x)
  have hfQ : Measurable fQ := measurable_from_quotient.mpr hf
  have hδ : Measurable δ := measurable_domainDensity F p hK hell
  have hT : MeasurableSet T := (hS.preimage (continuous_domainHeight F p hK)).measurableSet
  have hsq : Measurable (fun z => ‖fQ z‖ₑ ^ (2 : ℕ)) := hfQ.enorm.pow_const _
  have hquot : (∫⁻ z in T, δ z * ‖fQ z‖ₑ ^ (2 : ℕ) ∂domainHaarMeasure F p) < ∞ := by
    have h' : (∫⁻ z, ‖fQ z‖ₑ ^ (2 : ℕ) ∂domainMeasure F p hK ell T) < ∞ := by
      rw [lintegral_domainMeasure_eq_chamberDensity F p hK ell hell S hS.measurableSet hsq]
      exact hfin
    change (∫⁻ z, ‖fQ z‖ₑ ^ (2 : ℕ) ∂((domainHaarMeasure F p).restrict T).withDensity δ) < ∞ at h'
    rw [lintegral_withDensity_eq_lintegral_mul _ hδ hsq] at h'
    exact h'
  have hloc := (LeftCosetSpace.isQuotientCoveringMap_mk Γ hΓ).isCoveringMap
    |>.isLocalHomeomorph |>.isLocallyInjective
  intro x
  obtain ⟨r, hr⟩ := hcover x
  let e := Homeomorph.mulLeft (r : A)
  let y := e x
  obtain ⟨U, hUo, hyU, hUi⟩ := hloc y
  have hV : U ∩ hK.height ⁻¹' S ∈ 𝓝 y :=
    inter_mem (hUo.mem_nhds hyU) ((hS.preimage hK.continuous_height).mem_nhds hr)
  obtain ⟨C, ⟨hCn, hCc⟩, hCs⟩ := (compact_basis_nhds y).mem_iff.mp hV
  have hCm := hCc.isClosed.measurableSet
  let νC := (μG).restrict C
  have hCint : (∫⁻ g, δ (q g) * ‖f g‖ₑ ^ (2 : ℕ) ∂νC) < ∞ :=
    (LeftCosetSpace.lintegral_restrict_le_discreteQuotientMeasure Γ hΓ μG C hCm
      (hUi.mono fun _ hz => (hCs hz).1) T hT (fun _ hz => (hCs hz).2)
      (fun z => δ z * ‖fQ z‖ₑ ^ (2 : ℕ)) (hδ.mul hsq)).trans_lt hquot
  obtain ⟨M, hM⟩ := hCc.bddAbove_image (hell.comp hK.continuous_height).continuousOn
  let b := ENNReal.ofReal (Real.exp (-2 * M))
  have hb : 0 < b := ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hbd (g : A) (hg : g ∈ C) : b ≤ δ (q g) := by
    change ENNReal.ofReal (Real.exp (-2 * M)) ≤
      ENNReal.ofReal (Real.exp (-2 * ell (hK.height g)))
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left (hM ⟨g, hg, rfl⟩) (by norm_num)))
  have hprod : b * (∫⁻ g, ‖f g‖ₑ ^ (2 : ℕ) ∂νC) < ∞ := by
    rw [← lintegral_const_mul b (hf.enorm.pow_const _)]
    apply lt_of_le_of_lt (lintegral_mono_ae ?_) hCint
    filter_upwards [ae_restrict_mem hCm] with g hg
    exact mul_le_mul_left (hbd g hg) _
  have hf2 : MemLp f 2 νC := by
    have hfinite : (∫⁻ g, ‖f g‖ₑ ^ (2 : ℕ) ∂νC) ≠ ∞ := by
      intro htop
      rw [htop, ENNReal.mul_top hb.ne'] at hprod
      exact (lt_irrefl _ hprod)
    rw [memLp_iff]
    simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num)
      hf.aestronglyMeasurable, ENNReal.toReal_ofNat, ENNReal.rpow_two]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfinite
  let : IsFiniteMeasure νC := by
    refine ⟨?_⟩
    change (μG).restrict C univ < ∞
    rw [Measure.restrict_apply_univ]
    exact hCc.measure_lt_top
  have hiC : IntegrableOn f C μG := hf2.integrable (by norm_num)
  refine ⟨e ⁻¹' C, e.continuous.continuousAt.preimage_mem_nhds hCn, ?_⟩
  have hm : Measure.map e μG = μG := map_mul_left_eq_self μG r.val
  have he : f ∘ e = f := funext (hfinv r)
  rw [← he]
  apply (integrableOn_map_equiv e.toMeasurableEquiv).mp
  change IntegrableOn f C (Measure.map e μG)
  rwa [hm]

end Langlands.Global.WeightedSiegel
