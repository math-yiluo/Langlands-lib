import Langlands.Global.AdelicSpectralWitnessReduction
import Langlands.Global.AdelicWeightedConvolutionEstimate
import Langlands.Global.AdelicReproducingKernelStatement
import Langlands.Global.AdelicRationalConjugateCountingAllPointsStatement

/-! # Reduction of weighted moderate growth to a reproducing kernel and a point count

`weightedSquareIntegrableModerateGrowth_of_reduction` derives
`WeightedSquareIntegrableModerateGrowthStatement` (module `AdelicSpectralWitnessReduction`) from
`AdelicReproducingKernelStatement` (Harish-Chandra 1966, §8, Theorem 1) and
`AdelicRationalConjugateCountingAllPointsStatement` (Mœglin–Waldspurger I.2.4, Lemma (a)(i)),
by the argument of the proof of Mœglin–Waldspurger I.2.5, Lemma (b): fold the reproducing
integral onto `[G]` and apply the Cauchy–Schwarz inequality to the weighted norm. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set Topology
open scoped CategoryTheory.MonObj ENNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- A reproducing kernel (`AdelicReproducingKernelStatement`) and the count of rational points
in adelic conjugates of compact sets (`AdelicRationalConjugateCountingAllPointsStatement`) imply
that weighted square-integrable, smooth, `K_∞`-finite and `𝔷`-finite left `G(F)`-invariant
functions have moderate growth. -/
theorem weightedSquareIntegrableModerateGrowth_of_reduction
    (hR : AdelicReproducingKernelStatement)
    (hC : AdelicRationalConjugateCountingAllPointsStatement.{0}) :
    WeightedSquareIntegrableModerateGrowthStatement := by
  intro F _ _ G _ _ _ hred K N d rho hsmooth hcalc hKmax hrho _hP₀ μG m Φ hleft hsm hKfin hZfin
    hL2
  rcases Nat.eq_zero_or_pos N with hN | hN
  · -- A closed embedding into `GL_0` makes `G(𝔸)` trivial: a constant bound with `r = 0`.
    subst hN
    have hsub : Subsingleton (AdelicGroupPoints F G) :=
      ⟨fun _ _ => (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective
        (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩
    refine ⟨‖Φ 1‖ + 1, by positivity, 0, fun g => ?_⟩
    rw [Real.rpow_zero, mul_one, Subsingleton.elim g 1]
    linarith
  classical
  obtain ⟨A, hAc, hAs, hrep⟩ := hR F G hred K hsmooth hcalc hKmax Φ hleft hsm hKfin hZfin
  obtain ⟨e, hcount⟩ := hC F G N rho hN hrho
  have hΓd : IsDiscrete (rationalSubgroup F G : Set (AdelicGroupPoints F G)) :=
    isDiscrete_rationalSubgroup F G
  let : Countable (rationalSubgroup F G) := LeftCosetSpace.countable_of_isDiscrete _ hΓd
  have hCc : IsCompact (tsupport A) := hAs
  obtain ⟨B, hB, hBcount⟩ := hcount (tsupport A * (tsupport A)⁻¹) (hCc.mul hCc.inv)
  obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn
    (RepresentationGrowth.continuous_adelicHeight F G rho hN).continuousOn
  set L : ℝ := max 1 M with hLdef
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLC : ∀ a ∈ tsupport A, RepresentationGrowth.adelicHeight F G rho a ≤ L :=
    fun a ha => (le_abs_self _).trans ((hM a ha).trans (le_max_right _ _))
  have hht1 (g : AdelicGroupPoints F G) : 1 ≤ RepresentationGrowth.adelicHeight F G rho g :=
    RepresentationGrowth.one_le_adelicHeight F G rho hN g
  have hscal : (1 : ℝ) ≤ (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult) :=
    one_le_pow₀ (by exact_mod_cast hN)
  set f : RationalQuotient F G → ℂ :=
    fun y => Φ y.out / (rationalLogHeight F G rho y : ℂ) ^ m with hfdef
  have hf : MemLp f 2 μG := hL2
  have hσ1 (y : RationalQuotient F G) : 1 ≤ rationalLogHeight F G rho y := by
    have := Real.log_nonneg (le_max_left (1 : ℝ) (⨅ q : rationalSubgroup F G,
      RepresentationGrowth.adelicSourceNorm F G rho ((q : AdelicGroupPoints F G) * y.out)))
    simp only [rationalLogHeight]
    linarith
  -- On `x · supp A`, the value of `Φ` is controlled by `f` and a power of the height of `x`.
  have hpt (x a : AdelicGroupPoints F G) (ha : a ∈ tsupport A) :
      ‖Φ (x * a)‖ ≤ (L * RepresentationGrowth.adelicHeight F G rho x) ^ m *
        ‖f (LeftCosetSpace.mk (rationalSubgroup F G) (x * a))‖ := by
    set y := LeftCosetSpace.mk (rationalSubgroup F G) (x * a) with hy
    have hyout : LeftCosetSpace.mk (rationalSubgroup F G) y.out = y := Quotient.out_eq y
    have hγ : (x * a) * y.out⁻¹ ∈ rationalSubgroup F G :=
      (LeftCosetSpace.mk_eq_mk_iff _ _ _).mp hyout
    have hΦ : Φ y.out = Φ (x * a) := by
      have := hleft _ hγ y.out
      rw [inv_mul_cancel_right] at this
      exact this.symm
    have hσ : rationalLogHeight F G rho y ≤ L * RepresentationGrowth.adelicHeight F G rho x := by
      have hbdd : BddBelow (Set.range fun q : rationalSubgroup F G =>
          RepresentationGrowth.adelicSourceNorm F G rho ((q : AdelicGroupPoints F G) * y.out)) :=
        ⟨0, by
          rintro _ ⟨q, rfl⟩
          exact (RepresentationGrowth.adelicSourceNorm_pos F G rho hN _).le⟩
      have hinf : (⨅ q : rationalSubgroup F G,
          RepresentationGrowth.adelicSourceNorm F G rho ((q : AdelicGroupPoints F G) * y.out)) ≤
          RepresentationGrowth.adelicSourceNorm F G rho (x * a) := by
        have h := ciInf_le hbdd ⟨_, hγ⟩
        simpa only [inv_mul_cancel_right] using h
      have hsrc : RepresentationGrowth.adelicSourceNorm F G rho (x * a) ≤
          RepresentationGrowth.adelicHeight F G rho (x * a) := by
        rw [RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm]
        exact le_mul_of_one_le_left (RepresentationGrowth.adelicSourceNorm_pos F G rho hN _).le
          hscal
      have hmul : RepresentationGrowth.adelicHeight F G rho (x * a) ≤
          L * RepresentationGrowth.adelicHeight F G rho x := by
        calc RepresentationGrowth.adelicHeight F G rho (x * a)
            ≤ RepresentationGrowth.adelicHeight F G rho x *
                RepresentationGrowth.adelicHeight F G rho a :=
              RepresentationGrowth.adelicHeight_mul_le F G rho hN x a
          _ ≤ RepresentationGrowth.adelicHeight F G rho x * L :=
              mul_le_mul_of_nonneg_left (hLC a ha) (zero_le_one.trans (hht1 x))
          _ = L * RepresentationGrowth.adelicHeight F G rho x := mul_comm _ _
      have hT1 : 1 ≤ L * RepresentationGrowth.adelicHeight F G rho x :=
        one_le_mul_of_one_le_of_one_le hL1 (hht1 x)
      have hmax : max 1 (⨅ q : rationalSubgroup F G,
          RepresentationGrowth.adelicSourceNorm F G rho ((q : AdelicGroupPoints F G) * y.out)) ≤
          L * RepresentationGrowth.adelicHeight F G rho x :=
        max_le hT1 (hinf.trans (hsrc.trans hmul))
      have hlog := Real.log_le_log (zero_lt_one.trans_le (le_max_left _ _)) hmax
      have hlog' := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hT1)
      simp only [rationalLogHeight]
      linarith
    have hσpos : 0 < rationalLogHeight F G rho y := zero_lt_one.trans_le (hσ1 y)
    have hfy : ‖f y‖ * rationalLogHeight F G rho y ^ m = ‖Φ (x * a)‖ := by
      rw [hfdef]
      simp only
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hσpos.le, hΦ,
        div_mul_cancel₀ _ (pow_ne_zero _ hσpos.ne')]
    rw [← hfy, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hσpos.le hσ m) (norm_nonneg _)
  -- Folding: the translate of `supp A` covers `[G]` with multiplicity at most `B ‖x‖^e`.
  have hdom (x : AdelicGroupPoints F G) :
      Measure.map (fun a => LeftCosetSpace.mk (rationalSubgroup F G) (x * a))
          ((Measure.haar : Measure (AdelicGroupPoints F G)).restrict (tsupport A)) ≤
        ENNReal.ofReal (B * RepresentationGrowth.adelicHeight F G rho x ^ e) • μG := by
    obtain ⟨hPfin, hPcard⟩ := hBcount x
    let l : AdelicGroupPoints F G ≃ₜ AdelicGroupPoints F G := Homeomorph.mulLeft x
    let A' := l '' tsupport A
    let D := (fun y => x * y * x⁻¹) '' (tsupport A * (tsupport A)⁻¹)
    have hD : ∀ a ∈ A', ∀ c ∈ A', a * c⁻¹ ∈ D := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
      have hi : c⁻¹ ∈ (tsupport A)⁻¹ := by simpa using hc
      exact ⟨a * c⁻¹, mul_mem_mul ha hi, by simp [l, mul_assoc]⟩
    have hA'c : IsCompact A' := hCc.image l.continuous
    have hm := LeftCosetSpace.leftCosetSupportMeasure (rationalSubgroup F G)
      (Measure.haar : Measure (AdelicGroupPoints F G))
      (LeftCosetSpace.isFundamentalDomain (rationalSubgroup F G) hΓd Measure.haar)
      hA'c.isClosed.measurableSet MeasurableSet.univ (subset_univ _) hD
    rw [Measure.restrict_univ] at hm
    have htrans : Measure.map (fun a => LeftCosetSpace.mk (rationalSubgroup F G) (x * a))
        ((Measure.haar : Measure (AdelicGroupPoints F G)).restrict (tsupport A)) =
        Measure.map (LeftCosetSpace.mk (rationalSubgroup F G))
          ((Measure.haar : Measure (AdelicGroupPoints F G)).restrict A') := by
      change Measure.map (LeftCosetSpace.mk (rationalSubgroup F G) ∘ l) _ = _
      rw [← Measure.map_map (LeftCosetSpace.measurable_mk _) l.continuous.measurable]
      congr 1
      calc
        _ = ((Measure.haar : Measure (AdelicGroupPoints F G)).map l).restrict A' := by
          have heq := (l.toMeasurableEquiv.restrict_map
            (Measure.haar : Measure (AdelicGroupPoints F G)) A').symm
          change Measure.map l (Measure.restrict _ (l ⁻¹' A')) = _ at heq
          rwa [show l ⁻¹' A' = tsupport A from preimage_image_eq _ l.injective] at heq
        _ = (Measure.haar : Measure (AdelicGroupPoints F G)).restrict A' := by
          rw [show (Measure.haar : Measure (AdelicGroupPoints F G)).map l = Measure.haar from
            map_mul_left_eq_self _ x]
    have hmult : (((rationalSubgroup F G : Set (AdelicGroupPoints F G)) ∩ D).encard : ℝ≥0∞) ≤
        ENNReal.ofReal (B * RepresentationGrowth.adelicHeight F G rho x ^ e) := by
      rw [← Set.Finite.cast_ncard_eq hPfin, ENat.toENNReal_coe]
      have h := ENNReal.ofReal_le_ofReal hPcard
      rwa [ENNReal.ofReal_natCast] at h
    rw [htrans]
    refine hm.trans ?_
    refine Measure.le_iff.mpr fun V _ => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' hmult le_rfl
  -- Cauchy–Schwarz on `[G]`.
  let h : AdelicGroupPoints F G → ℂ := fun a => ((‖A a‖ : ℝ) : ℂ)
  have hhc : Continuous h := Complex.continuous_ofReal.comp hAc.norm
  have hhs : HasCompactSupport h :=
    hAs.comp_left (g := fun t : ℂ => ((‖t‖ : ℝ) : ℂ)) (by simp)
  have hh : MemLp h 2 ((Measure.haar : Measure (AdelicGroupPoints F G)).restrict (tsupport A)) :=
    (hhc.memLp_of_hasCompactSupport hhs).restrict _
  have hhC : Function.support h ⊆ tsupport A := fun a ha => subset_tsupport A (by
    simpa [h] using ha)
  let f' : RationalQuotient F G → ℂ := fun y => ((‖f y‖ : ℝ) : ℂ)
  have hf' : MemLp f' 2 μG := hf.norm.ofReal
  set cH : ℝ := ‖hh.toLp h‖ with hcH
  set cF : ℝ := ‖hf'.toLp f'‖ with hcF
  have hLx (x : AdelicGroupPoints F G) :
      0 ≤ (L * RepresentationGrowth.adelicHeight F G rho x) ^ m :=
    pow_nonneg (mul_nonneg (zero_le_one.trans hL1) (zero_le_one.trans (hht1 x))) m
  have hbound (x : AdelicGroupPoints F G) :
      ‖Φ x‖ ≤ (L * RepresentationGrowth.adelicHeight F G rho x) ^ m *
        (cH * (Real.sqrt (B * RepresentationGrowth.adelicHeight F G rho x ^ e) * cF)) := by
    have hqx : Measurable fun a => LeftCosetSpace.mk (rationalSubgroup F G) (x * a) :=
      (LeftCosetSpace.measurable_mk _).comp (measurable_const_mul x)
    obtain ⟨hint, hcs⟩ := norm_integral_mul_comp_le_of_map_restrict_le
      (Measure.haar : Measure (AdelicGroupPoints F G)) μG hqx
      (mul_nonneg hB (pow_nonneg (zero_le_one.trans (hht1 x)) e)) (hdom x) hh hhC hf'
    have hfun : (fun a => h a * f' (LeftCosetSpace.mk (rationalSubgroup F G) (x * a))) =
        fun a => ((‖A a‖ * ‖f (LeftCosetSpace.mk (rationalSubgroup F G) (x * a))‖ : ℝ) : ℂ) := by
      funext a
      simp [h, f']
    rw [hfun] at hint hcs
    rw [integral_complex_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (integral_nonneg fun a => by positivity)] at hcs
    have hreal : Integrable (fun a => ‖A a‖ *
        ‖f (LeftCosetSpace.mk (rationalSubgroup F G) (x * a))‖)
        (Measure.haar : Measure (AdelicGroupPoints F G)) := by
      refine hint.norm.congr (ae_of_all _ fun a => ?_)
      simp only [Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (by positivity)
    calc ‖Φ x‖ = ‖∫ a, Φ (x * a) * A a ∂(Measure.haar : Measure (AdelicGroupPoints F G))‖ := by
          rw [← hrep x]
      _ ≤ ∫ a, ‖Φ (x * a) * A a‖ ∂(Measure.haar : Measure (AdelicGroupPoints F G)) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ a, (L * RepresentationGrowth.adelicHeight F G rho x) ^ m *
            (‖A a‖ * ‖f (LeftCosetSpace.mk (rationalSubgroup F G) (x * a))‖)
            ∂(Measure.haar : Measure (AdelicGroupPoints F G)) := by
          refine integral_mono_of_nonneg (ae_of_all _ fun a => norm_nonneg _)
            (hreal.const_mul _) (ae_of_all _ fun a => ?_)
          show ‖Φ (x * a) * A a‖ ≤ (L * RepresentationGrowth.adelicHeight F G rho x) ^ m *
            (‖A a‖ * ‖f (LeftCosetSpace.mk (rationalSubgroup F G) (x * a))‖)
          by_cases ha : a ∈ tsupport A
          · rw [norm_mul]
            calc ‖Φ (x * a)‖ * ‖A a‖
                ≤ ((L * RepresentationGrowth.adelicHeight F G rho x) ^ m *
                    ‖f (LeftCosetSpace.mk (rationalSubgroup F G) (x * a))‖) * ‖A a‖ :=
                  mul_le_mul_of_nonneg_right (hpt x a ha) (norm_nonneg _)
              _ = _ := by ring
          · rw [image_eq_zero_of_notMem_tsupport ha, mul_zero, norm_zero]
            rw [zero_mul, mul_zero]
      _ = (L * RepresentationGrowth.adelicHeight F G rho x) ^ m *
            ∫ a, ‖A a‖ * ‖f (LeftCosetSpace.mk (rationalSubgroup F G) (x * a))‖
              ∂(Measure.haar : Measure (AdelicGroupPoints F G)) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hcs (hLx x)
  -- Convert the bound into the source norm with exponent `m + e`.
  have hcH0 : 0 ≤ cH := norm_nonneg _
  have hcF0 : 0 ≤ cF := norm_nonneg _
  set S : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult) with hS
  set K0 : ℝ := L ^ m * cH * Real.sqrt B * cF * S ^ (m + e) with hK0def
  have hK0 : 0 ≤ K0 := by positivity
  refine ⟨K0 + 1, by linarith, ((m + e : ℕ) : ℝ), fun x => ?_⟩
  rw [Real.rpow_natCast]
  set H := RepresentationGrowth.adelicHeight F G rho x with hH
  set s := RepresentationGrowth.adelicSourceNorm F G rho x with hs
  have hs0 : 0 ≤ s := (RepresentationGrowth.adelicSourceNorm_pos F G rho hN x).le
  have hHs : H = S * s := RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho x
  have hH1 : 1 ≤ H := hht1 x
  have hsq : Real.sqrt (B * H ^ e) ≤ Real.sqrt B * H ^ e := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt hB]
    have : H ^ e ≤ (H ^ e) ^ 2 := by
      nlinarith [one_le_pow₀ (n := e) hH1]
    exact mul_le_mul_of_nonneg_left this hB
  calc ‖Φ x‖ ≤ (L * H) ^ m * (cH * (Real.sqrt (B * H ^ e) * cF)) := hbound x
    _ ≤ (L * H) ^ m * (cH * ((Real.sqrt B * H ^ e) * cF)) := by gcongr
    _ = L ^ m * cH * Real.sqrt B * cF * H ^ (m + e) := by ring
    _ = K0 * s ^ (m + e) := by rw [hHs, mul_pow, hK0def]; ring
    _ ≤ (K0 + 1) * s ^ (m + e) := by nlinarith [pow_nonneg hs0 (m + e)]

end Langlands.Global
