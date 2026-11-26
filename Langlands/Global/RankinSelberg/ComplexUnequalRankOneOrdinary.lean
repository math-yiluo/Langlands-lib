import Langlands.Global.RankinSelberg.ComplexPlaceUnequalFunctionalEquationProof
import Langlands.Global.RankinSelberg.ComplexRankZeroLocal
import Langlands.Global.RankinSelberg.ComplexUnequalTranslatedNormalization
import Langlands.Representation.Whittaker.UpperUnipotentCharacterFactorization
import Mathlib.Analysis.Fourier.Inversion

/-! # Nonvanishing of complex unequal-rank tests with smaller rank one -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology FourierTransform Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal ComplexRankZero ComplexUnequalFamily ComplexJacquet
open Langlands.LocalFactor.Archimedean Langlands.RankinSelberg

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel

namespace ComplexUnequalRankOne

open Langlands.Whittaker.UpperUnipotentCharacter (adjacentUnit transvection_apply)
open ArchimedeanComplexPairFactor (complexLFactor_ne_zero)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexWhittakerTranslatedMellin (compact_rightTranslate_uniformSimpleRootBound)
open ComplexUnequalTranslatedNormalization (complexUnequalTranslatedNormalization)

local notation "G" => fun n => Langlands.GeneralLinear (n + 1) ℂ
local notation "Q" => LeftUnipotentQuotient 0 ℂ
local notation "ρ" => ArchimedeanLocal.translateFunction
local notation "Std" => fun n d => Automorphic.complexStandardKFinite (n + 1) d

private def firstRoot {r : ℕ} (h : 0 < r) (z : ℂ) :
    GeneralLinear.upperUnipotent (r + 1) ℂ :=
  adjacentUnit ⟨0, h⟩ z

private theorem character_firstRoot {r : ℕ} (h : 0 < r) (a : ℂˣ) (z : ℂ) :
    complexWhittakerCharacter a (firstRoot h z).val = (complexScaledCharacter a).complex z := by
  let i : Fin r := ⟨0, h⟩
  unfold complexWhittakerCharacter
  congr 1
  change (∑ j : Fin r, Matrix.transvection i.castSucc i.succ z j.castSucc j.succ) = z
  simp only [transvection_apply, ne_of_lt Fin.castSucc_lt_succ, ite_false, zero_add,
    Fin.castSucc_inj, Fin.succ_inj, and_self]
  simp

private theorem pad_mul_firstRoot {r : ℕ} (h : 0 < r) (g : G 0) (z : ℂ) :
    padGL (Nat.succ_le_succ h.le) g * (firstRoot h z).val =
      (firstRoot h (g.val.det * z)).val * padGL (Nat.succ_le_succ h.le) g := by
  let i : Fin r := ⟨0, h⟩
  let A := padGL (Nat.succ_le_succ h.le) g
  have hcol (k : Fin (r + 1)) : A.val k i.castSucc = if k = i.castSucc then g.val.det else 0 := by
    rw [UnequalAnalytic.padGL_apply]
    by_cases hk : k = i.castSucc
    · subst k
      have hi : i.castSucc.val < 1 := Nat.zero_lt_one
      rw [dite_eq_left ⟨hi, hi⟩, ite_eq_left rfl, Matrix.det_fin_one]
      rfl
    · have hk0 : ¬ k.val < 1 := by
        intro hk1
        apply hk
        exact Fin.ext (by change k.val = 0; omega)
      rw [dite_eq_right (fun h' => hk0 h'.1), Matrix.one_apply_ne hk, ite_eq_right hk]
  have hrow (k : Fin (r + 1)) : A.val i.succ k = if i.succ = k then 1 else 0 := by
    rw [UnequalAnalytic.padGL_apply, dite_eq_right (fun h' => by
      have h'1 := h'.1
      change 1 < 1 at h'1
      omega), Matrix.one_apply]
  apply Units.ext
  change A.val * (1 + Matrix.single i.castSucc i.succ z) =
    (1 + Matrix.single i.castSucc i.succ (g.val.det * z)) * A.val
  rw [mul_add, add_mul, mul_one, one_mul]
  congr 1
  ext k l
  by_cases hk : k = i.castSucc
  · subst k
    rw [Matrix.single_mul_apply_same, hrow]
    by_cases hl : l = i.succ
    · subst l
      rw [Matrix.mul_single_apply_same, hcol, ite_eq_left rfl, ite_eq_left rfl, mul_one]
    · rw [Matrix.mul_single_apply_of_ne z _ _ _ _ hl, ite_eq_right (Ne.symm hl), mul_zero]
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hk]
    by_cases hl : l = i.succ
    · subst l
      rw [Matrix.mul_single_apply_same, hcol, ite_eq_right hk, zero_mul]
    · rw [Matrix.mul_single_apply_of_ne z _ _ _ _ hl]

private theorem integrand_translate {r : ℕ} (h : 0 < r) {a : ℂˣ} {W : G r → ℂ}
    (hW : HasLeftCharacter a W) (V : G 0 → ℂ) (b s : ℂ) (q : Q) :
    complexUnequalIntegrand h (ρ (firstRoot h b).val W) V s q =
      (complexScaledCharacter a).complex ((quotientUnits q : ℂ) * b) *
        complexUnequalIntegrand h W V s q := by
  have hdet : (quotientUnits q : ℂ) = q.out.val.det := by
    exact congrArg Units.val ((congrArg quotientUnits (Quotient.out_eq q).symm).trans
      (quotientUnits_mk q.out))
  simp only [complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand,
    ArchimedeanLocal.translateFunction]
  rw [pad_mul_firstRoot h, hW _ _, character_firstRoot, hdet]
  simp only [mul_assoc]

private theorem fourier_eq_zero_of_character_integrals {f : ℂ → ℂ} (a : ℂˣ)
    (hzero : ∀ b : ℂ, (∫ z, (complexScaledCharacter a).complex (z * b) * f z) = 0) :
    𝓕 f = 0 := by
  funext w
  change 𝓕 f w = 0
  rw [Real.fourier_eq]
  let b : ℂ := -(star w) / (2 * (a : ℂ))
  have htrace (z : ℂ) : Algebra.trace ℝ ℂ ((a : ℂ) * (z * b)) = -(inner ℝ z w) := by
    have hmul : (a : ℂ) * (z * b) = -(z * star w) / 2 := by
      dsimp [b]
      field_simp [a.ne_zero]
    rw [hmul, Algebra.trace_complex_apply]
    simp [real_inner_comm, Complex.inner, Complex.div_ofNat_re]
    ring
  simp_rw [show ∀ z : ℂ, 𝐞 (-(inner ℝ z w)) • f z =
      (complexScaledCharacter a).complex (z * b) * f z by
    intro z
    rw [Circle.smul_def]
    change (Real.fourierChar (-(inner ℝ z w)) : ℂ) * f z =
      (complexScaledCharacter a (z * b) : ℂ) * f z
    rw [complexScaledCharacter_apply, htrace]]
  exact hzero b

private theorem analytic_eq_zero_on_right {f : ℂ → ℂ} {σ τ : ℝ}
    (hf : DifferentiableOn ℂ f {s | σ < s.re})
    (hzero : ∀ s : ℂ, τ < s.re → f s = 0) :
    ∀ s : ℂ, σ < s.re → f s = 0 := by
  let z₀ : ℂ := ((max σ τ + 1 : ℝ) : ℂ)
  have hz₀ : max σ τ < z₀.re := by simp [z₀]
  have hU : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  exact (hf.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_gt σ).isPreconnected ((le_max_left _ _).trans_lt hz₀)
    ((isOpen_lt continuous_const Complex.continuous_re).eventually_mem
      ((le_max_right _ _).trans_lt hz₀) |>.mono fun s hs => hzero s hs)

private theorem constant_rootBound {r : ℕ} {d : List ComplexCharacterData} {a : ℂˣ}
    (W : complexWhittakerModel r d a) :
    HasUniformSimpleRootBound (univ : Set ℂ) (fun _ => W.val) := by
  obtain ⟨N, hN⟩ := compact_rightTranslate_uniformSimpleRootBound W {1} isCompact_singleton
  refine ⟨N, fun J => ?_⟩
  obtain ⟨M, hM, hW⟩ := hN J
  refine ⟨M, hM, fun _ _ g => ?_⟩
  simpa only [mul_one] using hW 1 (mem_singleton _) g

private theorem unit_phase (a : ℂˣ) (b : ℂ) :
    Continuous (fun q : Q => (complexScaledCharacter a).complex ((quotientUnits q : ℂ) * b)) :=
  (complexScaledCharacter a).continuous_complex.comp
    ((Units.continuous_val.comp quotientUnits.continuous).mul_const b)

private theorem translated_integral_holomorphy {r : ℕ} (h : 0 < r)
    {d e : List ComplexCharacterData} {a : ℂˣ} (D : ComplexQuotientMeasureData 0)
    (W : complexWhittakerModel r d a) (V : complexWhittakerModel 0 e (-a)) :
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re →
      Integrable (complexUnequalIntegrand h W.val V.val s) D.measure) ∧
      ∀ b : ℂ,
        DifferentiableOn ℂ
          (complexUnequalIntegral h D (ρ (firstRoot h b).val W.val) V.val)
          {s : ℂ | σ < s.re} := by
  have hW : HasLeftCharacter a W.val :=
    fun u g => complexWhittakerModel_left_equivariant W.2 u.val u.2 g
  have hV : HasLeftCharacter (-a) V.val :=
    fun u g => complexWhittakerModel_left_equivariant V.2 u.val u.2 g
  have hWc := (contMDiff_of_mem_complexWhittakerModel W.2).continuous
  have hVc := (contMDiff_of_mem_complexWhittakerModel V.2).continuous
  obtain ⟨σ, hdom⟩ := ordinary_halfPlaneDomination h D (univ : Set ℂ)
    (fun _ => W.val) (fun _ => V.val) id
    (fun _ => hW) (fun _ => hV) (constant_rootBound W) (constant_rootBound V)
  refine ⟨σ, ?_, fun b => ?_⟩
  · intro s hs
    obtain ⟨M, hM, hbound⟩ := hdom s.re
    exact hM.mono' (continuous_ordinaryKernel h hW hV hWc hVc s).aestronglyMeasurable
      (ae_of_all _ (hbound s (mem_univ s) hs le_rfl))
  · let K := fun s => complexUnequalIntegrand h (ρ (firstRoot h b).val W.val) V.val s
    have hK : ∀ s q, K s q =
        (complexScaledCharacter a).complex ((quotientUnits q : ℂ) * b) *
          complexUnequalIntegrand h W.val V.val s q :=
      integrand_translate h hW V.val b
    have hdomK : HalfPlaneDomination D.measure univ id K σ := by
      intro τ
      obtain ⟨M, hM, hbound⟩ := hdom τ
      refine ⟨M, hM, fun s hs hσ hτ q => ?_⟩
      simpa only [hK, id_eq, norm_mul, HarmonicAnalysis.UnitaryAdditiveCharacter.norm_complex, one_mul]
        using hbound s hs hσ hτ q
    have hKc (s : ℂ) : Continuous (K s) := by
      rw [funext (hK s)]
      exact (unit_phase a b).mul (continuous_ordinaryKernel h hW hV hWc hVc s)
    have hKd (q : Q) : Differentiable ℂ (fun s => K s q) :=
      (differentiable_detPower_parameter q.out differentiable_id _).const_mul _
    have hd := (differentiableOn_integral_of_halfPlaneDomination isOpen_univ differentiable_id
      (fun s => (hKc s).aestronglyMeasurable) (fun q => (hKd q).differentiableOn) hdomK).2
    change DifferentiableOn ℂ (fun s => ∫ q, K s q ∂D.measure) _
    simpa only [univ_inter, id_eq] using hd

/-- If two compact-finite Whittaker coefficients are nonzero at the identity, with smaller rank
one, some compact-finite test with that smaller coefficient gives a nonzero ordinary integral
arbitrarily far to the right. -/
theorem exists_complexUnequalIntegral_rankOne_ne_zero_above {r : ℕ} (h : 0 < r)
    {d e : List ComplexCharacterData} (hd : d.length = r + 1) (he : e.length = 1)
    (a : ℂˣ) (D : ComplexQuotientMeasureData 0) (B : Std r d →ₗ[ℂ] (G r → ℂ))
    (hB : IsComplexWhittakerIntertwiner r d a B) (v : Std r d)
    (V : complexWhittakerModel 0 e (-a)) (hv : B v 1 ≠ 0) (hV₁ : V.val 1 ≠ 0) :
    ∃ U : complexWhittakerModel r d a, ∀ b : ℝ, ∃ s : ℂ,
      b < s.re ∧ complexUnequalIntegral h D U.val V.val s ≠ 0 := by
  by_contra! hzero
  let W : complexWhittakerModel r d a :=
    ⟨B v, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)⟩
  have hleft : HasLeftCharacter a W.val := fun u g => hB.1 v u.val u.2 g
  obtain ⟨σ, hint, hhol⟩ := translated_integral_holomorphy h D W V
  let s₀ : ℂ := ((σ + 1 : ℝ) : ℂ)
  have hs₀ : σ < s₀.re := by simp [s₀]
  have hTranslated (b : ℂ) :
      complexUnequalIntegral h D (ρ (firstRoot h b).val W.val) V.val s₀ = 0 := by
    obtain ⟨U, N, N₀, τ, hN, hRight, hLim, _, _, hRight₀⟩ :=
      complexUnequalTranslatedNormalization r 0 h d e a D
        (fun X Y => complexUnequalNormalizedGrowth r 0 h d e hd he a D X.val Y.val X.2 Y.2)
        B hB v (firstRoot h b).val V
    have hNzero (n : ℕ) : N n = 0 := by
      obtain ⟨p, hp⟩ := hzero (U n)
      ext z
      apply (show AnalyticOnNhd ℂ (N n) univ from fun s _ => (hN n).analyticAt s).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (mem_univ (((max p τ + 1 : ℝ) : ℂ))) _ (mem_univ z)
      have hs : max p τ < (((max p τ + 1 : ℝ) : ℂ)).re := by simp
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with s hs'
      rw [hRight n s ((le_max_right _ _).trans_lt hs'), hp s ((le_max_left _ _).trans_lt hs'),
        mul_zero, Pi.zero_apply]
    have hN₀zero (z : ℂ) : N₀ z = 0 := by
      have ht := (hLim.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (mem_univ z)
      have ht₀ : Tendsto (fun n => N n z) atTop (𝓝 0) := by
        simp only [hNzero, Pi.zero_apply, tendsto_const_nhds]
      exact tendsto_nhds_unique ht ht₀
    obtain ⟨p, hp⟩ := complexLFactor_ne_zero (complexPairBlocks d e)
    refine analytic_eq_zero_on_right (τ := max τ p) (hhol b) (fun s hs => ?_) s₀ hs₀
    exact (mul_eq_zero.mp ((hRight₀ s ((le_max_left _ _).trans_lt hs)).symm.trans (hN₀zero s))).resolve_left
      (hp s ((le_max_right _ _).trans_lt hs))
  let H := complexUnequalIntegrand h W.val V.val s₀
  let f (z : ℂ) : ℂ := (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * unitsExtend H z
  obtain ⟨κ, hκ, hmeasure⟩ := exists_measure_eq D
  have hf : Integrable f := (integrable_iff hκ hmeasure H).mp (hint s₀ hs₀)
  have hzeroF : ∀ b : ℂ, (∫ z, (complexScaledCharacter a).complex (z * b) * f z) = 0 := by
    intro b
    let I := complexUnequalIntegrand h (ρ (firstRoot h b).val W.val) V.val s₀
    have hη := integral_eq hmeasure I
    have hzerob : (∫ q, I q ∂D.measure) = 0 := hTranslated b
    rw [hzerob] at hη
    have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
    refine Eq.trans ?_ ((mul_eq_zero.mp hη.symm).resolve_left hκ')
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z = 0
    · simp [f, unitsExtend, hz]
    · let u := Units.mk0 z hz
      change (complexScaledCharacter a).complex (z * b) *
        ((((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * unitsExtend H u) =
          (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * unitsExtend I u
      rw [unitsExtend_val, unitsExtend_val]
      dsimp only [I, H]
      rw [integrand_translate h hleft,
        quotientUnits.apply_symm_apply]
      change _ = _ * ((complexScaledCharacter a).complex (z * b) * _)
      ac_rfl
  have hHc : Continuous H := continuous_ordinaryKernel h hleft
    (fun u g => complexWhittakerModel_left_equivariant V.2 u.val u.2 g)
    (hB.2.1 v).continuous (contMDiff_of_mem_complexWhittakerModel V.2).continuous s₀
  have hc : ContinuousAt f 1 := by
    change ContinuousAt f ((1 : ℂˣ) : ℂ)
    rw [← Units.isOpenEmbedding_val.continuousAt_iff]
    simp only [Function.comp_def, f, unitsExtend_val]
    have hnorm : ContinuousAt (fun u : ℂˣ => ‖(u : ℂ)‖ ^ 2) 1 :=
      (Units.continuous_val.norm.pow 2).continuousAt
    exact (Complex.continuous_ofReal.continuousAt.comp
      (hnorm.inv₀ (by simp))).mul (hHc.comp quotientUnits.symm.continuous).continuousAt
  have hFourier := fourier_eq_zero_of_character_integrals a hzeroF
  have hf₁ : f 1 = 0 := by
    have hinv := hf.fourierInv_fourier_eq (hFourier.symm ▸ integrable_zero _ _ _) hc
    simpa [hFourier, Real.fourierInv_eq] using hinv.symm
  have hq : (quotientUnits.symm 1).out = (1 : G 0) := by rw [quotientUnits_symm_out, map_one]
  apply mul_ne_zero (mul_ne_zero hv hV₁) (Complex.exp_ne_zero _)
  change (((‖((1 : ℂˣ) : ℂ)‖ ^ 2)⁻¹ : ℝ) : ℂ) * unitsExtend H (1 : ℂˣ) = 0 at hf₁
  rw [unitsExtend_val] at hf₁
  simpa only [Units.val_one, norm_one, one_pow, inv_one, Complex.ofReal_one, one_mul,
    H, complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, hq, map_one, W,
    ArchimedeanLocal.detPower] using hf₁

end ComplexUnequalRankOne

end Langlands.Global.RankinSelbergGlobal
