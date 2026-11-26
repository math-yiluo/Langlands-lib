import Langlands.Global.AdelicWavePacketProductPairingStatement
import Langlands.Global.AdelicAmbientWavePacketProfileProof
import Langlands.Global.AdelicPrincipalQuotientProductMeasureStatement
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Transport and factorization of the wave-packet pairing -/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global

open GroupScheme AdelicGroupPoints RestrictionSplitCentre

private theorem memLp_two_iff_sq_lintegral_lt_top {X : Type*} [MeasurableSpace X]
    {measure : Measure X} {f : X → ℂ} (hf : AEStronglyMeasurable f measure) :
    MemLp f 2 measure ↔ (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂measure) < ∞ := by
  rw [memLp_two_iff_integrable_sq_norm hf, Integrable, hasFiniteIntegral_iff_enorm,
    and_iff_right (hf.norm.aemeasurable.pow_const 2).aestronglyMeasurable]
  simp only [Real.enorm_eq_ofReal (sq_nonneg _)]

private theorem memLp_two_profile_prod_of_aesm {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {α : Measure X} {β : Measure Y} [SFinite α] [SFinite β] {u : X → ℂ} {f : Y → ℂ}
    (hu : MemLp u 2 α) (hpos : 0 < ∫ x, ‖u x‖ ^ 2 ∂α) (hf : AEStronglyMeasurable f β) :
    MemLp (fun z : X × Y => u z.1 * f z.2) 2 (α.prod β) ↔ MemLp f 2 β := by
  have huf : AEStronglyMeasurable (fun z : X × Y => u z.1 * f z.2) (α.prod β) :=
    (hu.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
      (hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hint := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have hαpos : 0 < ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂α := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg ‖u x‖)]
    exact ENNReal.ofReal_pos.mpr hpos
  have hαfin := (memLp_two_iff_sq_lintegral_lt_top hu.aestronglyMeasurable).mp hu
  rw [memLp_two_iff_sq_lintegral_lt_top huf, memLp_two_iff_sq_lintegral_lt_top hf]
  simp only [norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
  rw [lintegral_prod_mul (hu.aestronglyMeasurable.norm.aemeasurable.pow_const 2).ennreal_ofReal
    (hf.norm.aemeasurable.pow_const 2).ennreal_ofReal]
  exact ⟨fun h => ENNReal.lt_top_of_mul_ne_top_right h.ne hαpos.ne', ENNReal.mul_lt_top hαfin⟩

/-- A nonzero section of the product determines relative measurability. -/
private theorem memLp_two_profile_prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {α : Measure X} {β : Measure Y} [SFinite α] [SFinite β] {u : X → ℂ} {f : Y → ℂ}
    (hu : MemLp u 2 α) (hpos : 0 < ∫ x, ‖u x‖ ^ 2 ∂α) :
    MemLp (fun z : X × Y => u z.1 * f z.2) 2 (α.prod β) ↔ MemLp f 2 β := by
  refine ⟨fun h => ?_, fun h => (memLp_two_profile_prod_of_aesm hu hpos h.aestronglyMeasurable).mpr h⟩
  have hsec : ∀ᵐ x ∂α, AEStronglyMeasurable (fun y => u x * f y) β :=
    h.aestronglyMeasurable.prodMk_left
  have hnonzero : ¬ (∀ᵐ x ∂α, u x = 0) := by
    intro hzero
    have heq : ∫ x, ‖u x‖ ^ 2 ∂α = ∫ _ : X, (0 : ℝ) ∂α :=
      integral_congr_ae (hzero.mono fun x hx => by simp [hx])
    simp only [integral_zero] at heq
    exact hpos.ne' heq
  obtain ⟨x, hxu, hx⟩ : ∃ x, u x ≠ 0 ∧ AEStronglyMeasurable (fun y => u x * f y) β := by
    by_contra! hnone
    apply hnonzero
    filter_upwards [hsec] with x hx
    by_contra hx0
    exact hnone x hx0 hx
  have hm : AEStronglyMeasurable (fun y => (u x)⁻¹ * (u x * f y)) β :=
    aestronglyMeasurable_const.mul hx
  have hf : AEStronglyMeasurable f β := by
    simpa only [← mul_assoc, inv_mul_cancel₀ hxu, one_mul] using hm
  exact (memLp_two_profile_prod_of_aesm hu hpos hf).mp h

set_option maxHeartbeats 600000 in
/-- The exact quotient product transports both the square norm and the pairing. -/
theorem wavePacketProductPairing_of_productMeasure
    (hPM : PrincipalQuotientProductMeasureStatement) : WavePacketProductPairingStatement := by
  intro F _ _ G _ _ hG m eG b hb hbc hb0
  let α := positiveCentreHaarMeasure F G hG
  let ν := canonicalMeasure F G
  let fullMeasure := rationalQuotientHaarMeasure F G
  let E := principalQuotientProductEquiv F G hG
  let A : canonicalSubgroup F G → ℂ := fun a => ambientWavePacketProfile eG b a.val
  have ⟨_, hA, hpos⟩ := ambientWavePacketProfile_squareIntegrable F G hG eG b hb hbc
  have hmass : 0 < ∫ a, ‖A a‖ ^ 2 ∂α := hpos hb0
  have hE : MeasurePreserving E fullMeasure (α.prod ν) := hPM F G hG
  have : SigmaFinite α := by
    unfold α positiveCentreHaarMeasure
    exact (positiveCentreEquiv F G hG).toHomeomorph.toMeasurableEquiv.sigmaFinite_map
  have : SFinite ν := by
    unfold ν canonicalMeasure quotientHaarMeasure normOneRationalQuotientHaarMeasure
      LeftCosetSpace.haarQuotientMeasure LeftCosetSpace.discreteQuotientMeasure
      LeftCosetSpace.quotientMeasure
    infer_instance
  refine ⟨hmass, ?_, ?_, ?_⟩
  · intro f g
    obtain ⟨⟨t, n⟩, ht⟩ := (intrinsicNormOneDecomposition F G hG).surjective g
    let a := positiveCentreEquiv F G hG t
    have hg : g = a.val * n.val := ht.symm
    have hlog : characterLog F G g = characterLog F G a.val := by
      rw [hg, characterLog_mul, (characterLog_eq_zero_iff F G _).mpr n.property, add_zero]
    have hp : ambientWavePacketProfile eG b g = ambientWavePacketProfile eG b a.val := by
      simp only [ambientWavePacketProfile, parameterPower, hlog]
    have hfirst : (principalQuotientProductHomeomorph F G hG
        (LeftCosetSpace.mk (rationalSubgroup F G) g)).1 = a := by
      rw [hg, principalQuotientProductHomeomorph_mk]
    rw [ambientProfileQuotientLift, coe_principalQuotientProductEquiv, hfirst,
      principalQuotientProductHomeomorph_snd_mk, hp]
  · intro f
    let ψ : canonicalSubgroup F G × CanonicalQuotient F G → ℂ := fun z => A z.1 * f z.2
    change MemLp (ψ ∘ E) 2 fullMeasure ↔ MemLp f 2 ν
    have heq : MemLp ψ 2 (α.prod ν) ↔ MemLp (ψ ∘ E) 2 fullMeasure := by
      rw [← hE.map_eq, E.memLp_map_measure_iff]
    rw [← heq]
    exact memLp_two_profile_prod hA hmass
  · intro f g _ _
    calc
      _ = ∫ z : canonicalSubgroup F G × CanonicalQuotient F G,
          (A z.1 * f z.2) * (starRingEnd ℂ) (A z.1 * g z.2) ∂(α.prod ν) :=
        hE.integral_comp' _
      _ = ∫ z : canonicalSubgroup F G × CanonicalQuotient F G,
          ((‖A z.1‖ ^ 2 : ℝ) : ℂ) * (f z.2 * (starRingEnd ℂ) (g z.2)) ∂(α.prod ν) := by
        apply integral_congr_ae
        filter_upwards with z
        rw [map_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
        ac_rfl
      _ = _ := by
        rw [integral_prod_mul (fun a : canonicalSubgroup F G => ((‖A a‖ ^ 2 : ℝ) : ℂ))
          (fun y : CanonicalQuotient F G => f y * (starRingEnd ℂ) (g y)), integral_complex_ofReal]

end Langlands.Global
