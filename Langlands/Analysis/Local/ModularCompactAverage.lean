import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.Basic

/-!
# Compact averages of modular-covariant functions

For a closed subgroup `P` of a second countable locally compact group `G` with a
right invariant Haar measure, and a compact open subgroup `K` with `G = P K`, the
integral over `K` of a continuous function that is left covariant under `P` by the
modular character of `P` is invariant under every right translation.
-/

noncomputable section

namespace Langlands.ModularCompactAverage

open MeasureTheory Measure Set Function
open scoped NNReal ENNReal

universe u

section Character

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [SecondCountableTopology H]

/-- Right translation scales every Haar measure by Mathlib's modular character. -/
theorem map_mul_right_eq_modularCharacter_smul [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [IsHaarMeasure μ] (q : H) :
    map (· * q) μ = modularCharacter q • μ := by
  change map (· * q) μ = modularCharacterFun q • μ
  rw [modularCharacterFun_eq_haarScalarFactor μ q]
  exact isMulLeftInvariant_eq_smul _ μ

/-- The modular character is trivial on every compact open subgroup. -/
theorem modularCharacter_eq_one_of_mem (U : Subgroup H) (hUo : IsOpen (U : Set H))
    (hUc : IsCompact (U : Set H)) {u : H} (hu : u ∈ U) : modularCharacter u = 1 := by
  borelize H
  let μ : Measure H := haar
  have hmap := map_mul_right_eq_modularCharacter_smul μ u
  have hpre : (· * u) ⁻¹' (U : Set H) = U := by
    ext x
    simp [U.mul_mem_cancel_right hu]
  have h := congrArg (fun ν : Measure H => ν U) hmap
  simp only [Measure.smul_apply, nnreal_smul_coe_apply] at h
  rw [map_apply (measurable_mul_const u) hUo.measurableSet, hpre] at h
  have hpos : μ U ≠ 0 := (hUo.measure_pos μ ⟨1, U.one_mem⟩).ne'
  have hfin : μ U ≠ ∞ := hUc.measure_lt_top.ne
  have h1 : ((modularCharacter u : ℝ≥0) : ℝ≥0∞) = 1 :=
    (ENNReal.mul_eq_right hpos hfin).mp h.symm
  exact_mod_cast h1

/-- Conjugation scales every Haar measure by Mathlib's modular character. -/
theorem measure_preimage_conj [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [IsHaarMeasure μ] (z : H) {S : Set H} (hS : MeasurableSet S) :
    μ ((fun p => z⁻¹ * p * z) ⁻¹' S) = modularCharacter z * μ S := by
  have h1 : (fun p => z⁻¹ * p * z) ⁻¹' S = (fun p => z⁻¹ * p) ⁻¹' ((fun p => p * z) ⁻¹' S) :=
    rfl
  rw [h1, measure_preimage_mul, ← Measure.map_apply (measurable_mul_const _) hS,
    map_mul_right_eq_modularCharacter_smul μ, Measure.smul_apply, nnreal_smul_coe_apply]

end Character

section Average

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- **Compact averaging of modular-covariant functions.** Let `μ` be a right invariant
Haar measure on `G`, `P` a closed subgroup, and `K` a compact open subgroup with
`G = P K`. If `φ` is continuous and `φ (q * x) = Δ_P(q) φ x` for the modular
character `Δ_P` of `P`, then `∫_K φ (x g) dμ = ∫_K φ dμ` for every `g`. -/
theorem setIntegral_mul_right_eq (μ : Measure G) [IsHaarMeasure μ] [IsMulRightInvariant μ]
    (P : Subgroup G) (hP : IsClosed (P : Set G)) [LocallyCompactSpace P]
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
    (φ : G → ℂ) (hφ : Continuous φ)
    (hcov : ∀ (q : P) (x : G),
      φ ((q : G) * x) = (((modularCharacter q : ℝ≥0) : ℝ) : ℂ) * φ x)
    (g : G) :
    ∫ x in (K : Set G), φ (x * g) ∂μ = ∫ x in (K : Set G), φ x ∂μ := by
  classical
  have : SecondCountableTopology P := TopologicalSpace.Subtype.secondCountableTopology _
  let _ : MeasurableSpace P := borel P
  have : BorelSpace P := ⟨rfl⟩
  let ν : Measure P := haar
  let Δ : P → ℂ := fun q => (((modularCharacter q : ℝ≥0) : ℝ) : ℂ)
  let χ : G → ℂ := (K : Set G).indicator 1
  have hKmeas : MeasurableSet (K : Set G) := hKo.measurableSet
  have hKclopen : IsClopen (K : Set G) := ⟨K.isClosed_of_isOpen hKo, hKo⟩
  have hχ : Continuous χ := hKclopen.continuous_indicator continuous_const
  have hχapp (y : G) : χ y = if y ∈ K then 1 else 0 := by
    simp only [χ, Set.indicator, SetLike.mem_coe, Pi.one_apply]
  let C : Set P := Subtype.val ⁻¹' (K : Set G)
  have hCo : IsOpen C := hKo.preimage continuous_subtype_val
  have hCc : IsCompact C := hP.isClosedEmbedding_subtypeVal.isCompact_preimage hKc
  have hCmeas : MeasurableSet C := hCo.measurableSet
  have hνC0 : ν C ≠ 0 := (hCo.measure_pos ν ⟨1, K.one_mem⟩).ne'
  have hνCtop : ν C ≠ ∞ := hCc.measure_lt_top.ne
  have hνCreal : ν.real C ≠ 0 := by
    rw [measureReal_def]
    exact ENNReal.toReal_ne_zero.mpr ⟨hνC0, hνCtop⟩
  have hΔC (c : P) (hc : c ∈ C) : modularCharacter c = 1 :=
    modularCharacter_eq_one_of_mem (K.comap P.subtype) hCo hCc hc
  -- Iwasawa-type factorization of an arbitrary element.
  have hfac (y : G) : ∃ q : P, ∃ k ∈ K, y = (q : G) * k := by
    obtain ⟨q, hq, k, hk, h⟩ := hPK y
    exact ⟨⟨q, hq⟩, k, hk, h⟩
  -- The mass of the inner `P`-integral in the first order of integration.
  have hinner₁ (y : G) : ∫ p : P, χ ((p : G)⁻¹ * y * g⁻¹) ∂ν = ν.real C := by
    obtain ⟨q, k, hk, hy⟩ := hfac (y * g⁻¹)
    have hfun : (fun p : P => χ ((p : G)⁻¹ * y * g⁻¹)) =
        ((fun p : P => q⁻¹ * p) ⁻¹' C).indicator (fun _ => (1 : ℂ)) := by
      funext p
      have hiff : (p : G)⁻¹ * y * g⁻¹ ∈ K ↔ ((q⁻¹ * p : P) : G) ∈ K := by
        rw [mul_assoc, hy, ← mul_assoc, K.mul_mem_cancel_right hk, ← K.inv_mem_iff]
        simp
      by_cases hp : ((q⁻¹ * p : P) : G) ∈ K
      · simp only [hχapp, hiff.mpr hp, ↓reduceIte]
        rw [Set.indicator_of_mem (by exact hp)]
      · simp only [hχapp, show ¬ _ from fun h => hp (hiff.mp h), ↓reduceIte]
        rw [Set.indicator_of_notMem (by exact hp)]
    rw [hfun, integral_indicator_const _ ((measurable_const_mul q⁻¹) hCmeas)]
    simp only [measureReal_def, measure_preimage_mul]
    simp [Complex.real_smul]
  -- The mass of the inner `P`-integral in the second order of integration.
  have hinner₂ (z : G) : ∫ p : P, Δ p * χ ((p : G) * z) ∂ν = ν.real C := by
    obtain ⟨q, k, hk, hz⟩ := hfac z
    let f : P → ℂ := C.indicator (fun r => Δ (r * q⁻¹))
    have hfun : (fun p : P => Δ p * χ ((p : G) * z)) = fun p => f (p * q) := by
      funext p
      have hiff : (p : G) * z ∈ K ↔ ((p * q : P) : G) ∈ K := by
        rw [hz, ← mul_assoc, K.mul_mem_cancel_right hk]
        rfl
      by_cases hp : ((p * q : P) : G) ∈ K
      · simp only [hχapp, hiff.mpr hp, ↓reduceIte, mul_one]
        simp only [f, Set.indicator_of_mem (show p * q ∈ C from hp), mul_inv_cancel_right]
      · simp only [hχapp, show ¬ _ from fun h => hp (hiff.mp h), ↓reduceIte, mul_zero]
        simp only [f, Set.indicator_of_notMem (show p * q ∉ C from hp)]
    have hf : f = C.indicator (fun _ => Δ q⁻¹) := by
      apply Set.indicator_congr
      intro r hr
      simp only [Δ, map_mul, hΔC r hr, one_mul]
    rw [hfun]
    have hmapq : map (· * q) ν = modularCharacter q • ν :=
      map_mul_right_eq_modularCharacter_smul ν q
    have hint : ∫ p : P, f (p * q) ∂ν = ∫ p : P, f p ∂(map (· * q) ν) :=
      (integral_map_equiv (MeasurableEquiv.mulRight q) f).symm
    rw [hint, hmapq, integral_smul_nnreal_measure, hf, integral_indicator_const _ hCmeas]
    have hΔinv : (((modularCharacter q : ℝ≥0) : ℝ) : ℂ) * Δ q⁻¹ = 1 := by
      simp only [Δ, map_inv]
      push_cast
      rw [mul_inv_cancel₀]
      exact_mod_cast (modularCharacterFun_pos q).ne'
    rw [NNReal.smul_def, Complex.real_smul, Complex.real_smul]
    calc (((modularCharacter q : ℝ≥0) : ℝ) : ℂ) * ((ν.real C : ℂ) * Δ q⁻¹)
        = (ν.real C : ℂ) * ((((modularCharacter q : ℝ≥0) : ℝ) : ℂ) * Δ q⁻¹) := by ring
      _ = ν.real C := by rw [hΔinv, mul_one]
  -- Both sides as integrals over `G` against the indicator `χ` of `K`.
  have hLHS : ∫ x in (K : Set G), φ (x * g) ∂μ = ∫ y, χ (y * g⁻¹) * φ y ∂μ := by
    rw [← integral_indicator hKmeas]
    have hfun : (K : Set G).indicator (fun x => φ (x * g)) =
        fun x => (fun y => χ (y * g⁻¹) * φ y) (x * g) := by
      funext x
      by_cases hx : x ∈ K <;> simp [hχapp, hx]
    rw [hfun, integral_mul_right_eq_self (fun y => χ (y * g⁻¹) * φ y) g]
  have hRHS : ∫ x in (K : Set G), φ x ∂μ = ∫ y, χ y * φ y ∂μ := by
    rw [← integral_indicator hKmeas]
    congr 1
    funext x
    by_cases hx : x ∈ K <;> simp [hχapp, hx]
  -- The compact set `K g⁻¹ K` of `G` and its preimage in `P`.
  let S : Set G := (fun ab : G × G => ab.1 * g⁻¹ * ab.2) '' ((K : Set G) ×ˢ (K : Set G))
  have hSc : IsCompact S :=
    (hKc.prod hKc).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  have hSPc : IsCompact (Subtype.val ⁻¹' S : Set P) :=
    hP.isClosedEmbedding_subtypeVal.isCompact_preimage hSc
  -- First order of integration.
  let F₁ : G → P → ℂ := fun y p => φ y * χ y * χ ((p : G)⁻¹ * y * g⁻¹)
  have hF₁ : Integrable (uncurry F₁) (μ.prod ν) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hφ.comp continuous_fst).mul (hχ.comp continuous_fst)).mul
        (hχ.comp (((continuous_subtype_val.comp continuous_snd).inv.mul
          continuous_fst).mul continuous_const))
    · refine HasCompactSupport.intro (hKc.prod hSPc) ?_
      rintro ⟨y, p⟩ hyp
      simp only [uncurry_apply_pair, F₁, hχapp]
      by_cases hy : y ∈ K
      · by_cases hk : (p : G)⁻¹ * y * g⁻¹ ∈ K
        · exfalso
          refine hyp ⟨hy, ⟨y, ((p : G)⁻¹ * y * g⁻¹)⁻¹⟩, ⟨hy, K.inv_mem hk⟩, ?_⟩
          show y * g⁻¹ * ((p : G)⁻¹ * y * g⁻¹)⁻¹ = p
          group
        · simp [hk]
      · simp [hy]
  -- Second order of integration.
  let F₂ : P → G → ℂ := fun p z => φ ((p : G) * z) * χ ((p : G) * z) * χ (z * g⁻¹)
  have hF₂ : Integrable (uncurry F₂) (ν.prod μ) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · have hpz : Continuous fun pz : P × G => (pz.1 : G) * pz.2 :=
        (continuous_subtype_val.comp continuous_fst).mul continuous_snd
      exact ((hφ.comp hpz).mul (hχ.comp hpz)).mul
        (hχ.comp (continuous_snd.mul continuous_const))
    · refine HasCompactSupport.intro (hSPc.prod (hKc.image (continuous_mul_const g))) ?_
      rintro ⟨p, z⟩ hpz
      simp only [uncurry_apply_pair, F₂, hχapp]
      by_cases h₁ : (p : G) * z ∈ K
      · by_cases h₂ : z * g⁻¹ ∈ K
        · exfalso
          refine hpz ⟨⟨⟨(p : G) * z, (z * g⁻¹)⁻¹⟩, ⟨h₁, K.inv_mem h₂⟩, ?_⟩,
            ⟨z * g⁻¹, h₂, by simp⟩⟩
          show (p : G) * z * g⁻¹ * (z * g⁻¹)⁻¹ = p
          group
        · simp [h₂]
      · simp [h₁]
  have hI₁ : ∫ y, ∫ p : P, F₁ y p ∂ν ∂μ = (ν.real C : ℂ) * ∫ y, χ y * φ y ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext y
    simp only [F₁]
    rw [integral_const_mul, hinner₁]
    ring
  have hswap : ∫ p : P, ∫ y, F₁ y p ∂μ ∂ν = ∫ p : P, ∫ z, F₂ p z ∂μ ∂ν := by
    congr 1
    funext p
    rw [← integral_mul_left_eq_self (F₁ · p) (p : G)]
    congr 1
    funext z
    simp only [F₁, F₂]
    congr 2
    group
  have hI₂ : ∫ z, ∫ p : P, F₂ p z ∂ν ∂μ = (ν.real C : ℂ) * ∫ y, χ (y * g⁻¹) * φ y ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext z
    have hpt : (fun p : P => F₂ p z) = fun p => (χ (z * g⁻¹) * φ z) * (Δ p * χ ((p : G) * z)) := by
      funext p
      simp only [F₂, hcov, Δ]
      ring
    rw [hpt, integral_const_mul, hinner₂]
    ring
  have hmain : (ν.real C : ℂ) * ∫ y, χ y * φ y ∂μ =
      (ν.real C : ℂ) * ∫ y, χ (y * g⁻¹) * φ y ∂μ := by
    rw [← hI₁, integral_integral_swap hF₁, hswap, integral_integral_swap hF₂, hI₂]
  rw [hLHS, hRHS]
  exact (mul_left_cancel₀ (by exact_mod_cast hνCreal) hmain).symm

end Average

end Langlands.ModularCompactAverage
