import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.UniformRing

/-!
# Completions of number fields at dense nonarchimedean embeddings

A ring embedding `j : K →+* F` of a number field into a complete nonarchimedean
nontrivially normed field with dense image determines a finite prime of `K`, and the
corresponding adic completion is identified with `F` by a ring isomorphism that is
continuous in both directions and extends `j`.
-/

namespace Langlands.Global.FieldRealization

open IsDedekindDomain NumberField Topology Filter UniformSpace

variable {K : Type*} [Field K] [NumberField K]
  {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]

omit [NumberField K] in
/-- Algebraic integers have norm at most one under a nonarchimedean embedding. -/
theorem norm_ringOfIntegers_le_one (j : K →+* F) (a : 𝓞 K) : ‖j a‖ ≤ 1 := by
  let w : Valuation F NNReal := NormedField.valuation
  have hw := Valuation.integer.integers w
  have h₁ : IsIntegral ℤ (j a) := (RingOfIntegers.isIntegral_coe a).map j.toIntAlgHom
  have h₂ : IsIntegral w.integer (j a) := h₁.tower_top
  have h₃ := hw.mem_of_integral h₂
  rw [Valuation.mem_integer_iff] at h₃
  exact_mod_cast h₃

omit [NumberField K] in
/-- A dense nonarchimedean embedding has nonzero elements of arbitrarily small norm. -/
theorem exists_ne_zero_norm_lt (j : K →+* F) (hj : DenseRange j) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : K, x ≠ 0 ∧ ‖j x‖ < ε := by
  obtain ⟨y, hy0, hyε⟩ := NormedField.exists_norm_lt F hε
  obtain ⟨x, hx⟩ := hj.exists_dist_lt y hy0
  rw [dist_eq_norm, norm_sub_rev] at hx
  refine ⟨x, ?_, ?_⟩
  · rintro rfl
    simp at hx
  · calc ‖j x‖ = ‖(j x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ max ‖j x - y‖ ‖y‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < ε := max_lt (hx.trans hyε) hyε

/-- The prime ideal of algebraic integers of norm less than one. -/
def normLtOneIdeal (j : K →+* F) : Ideal (𝓞 K) where
  carrier := {a | ‖j (algebraMap (𝓞 K) K a)‖ < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, norm_mul] at ha ⊢
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_ringOfIntegers_le_one j c)).trans_lt ha

omit [NumberField K] in
theorem mem_normLtOneIdeal (j : K →+* F) (a : 𝓞 K) :
    a ∈ normLtOneIdeal j ↔ ‖j a‖ < 1 := Iff.rfl

omit [NumberField K] in
theorem normLtOneIdeal_isPrime (j : K →+* F) : (normLtOneIdeal j).IsPrime where
  ne_top' h := by
    have h1 : (1 : 𝓞 K) ∈ normLtOneIdeal j := h ▸ Submodule.mem_top
    simp [mem_normLtOneIdeal] at h1
  mem_or_mem' {a b} hab := by
    simp only [mem_normLtOneIdeal, RingOfIntegers.coe_eq_algebraMap, map_mul, norm_mul] at hab ⊢
    by_contra h
    push Not at h
    have ha := le_antisymm (norm_ringOfIntegers_le_one j a) h.1
    have hb := le_antisymm (norm_ringOfIntegers_le_one j b) h.2
    rw [ha, hb, one_mul] at hab
    exact lt_irrefl _ hab

theorem normLtOneIdeal_ne_bot (j : K →+* F) (hj : DenseRange j) : normLtOneIdeal j ≠ ⊥ := by
  obtain ⟨x, hx0, hx1⟩ := exists_ne_zero_norm_lt j hj one_pos
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hd0 : algebraMap (𝓞 K) K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hx0
  intro hbot
  have hn : n ∈ normLtOneIdeal j := by
    rw [mem_normLtOneIdeal]
    have hdle := norm_ringOfIntegers_le_one j d
    rw [map_div₀, norm_div] at hx1
    have hpos : 0 < ‖j (algebraMap (𝓞 K) K d)‖ := by
      rw [norm_pos_iff]
      exact (map_ne_zero j).mpr hd0
    rw [div_lt_one hpos] at hx1
    exact hx1.trans_le hdle
  rw [hbot, Ideal.mem_bot] at hn
  exact hn0 hn

/-- The finite prime of `K` determined by a dense nonarchimedean embedding. -/
def densePrime (j : K →+* F) (hj : DenseRange j) : HeightOneSpectrum (𝓞 K) where
  asIdeal := normLtOneIdeal j
  isPrime := normLtOneIdeal_isPrime j
  ne_bot := normLtOneIdeal_ne_bot j hj

theorem mem_densePrime (j : K →+* F) (hj : DenseRange j) (a : 𝓞 K) :
    a ∈ (densePrime j hj).asIdeal ↔ ‖j a‖ < 1 := Iff.rfl

section Comparison

variable (j : K →+* F) (hj : DenseRange j)

theorem norm_le_one_of_valuation_le_one {x : K}
    (hx : (densePrime j hj).valuation K x ≤ 1) : ‖j x‖ ≤ 1 := by
  obtain ⟨n, d, hnd⟩ := (densePrime j hj).exists_primeCompl_mul_eq_of_integer x hx
  have hd : ‖j (algebraMap (𝓞 K) K d)‖ = 1 :=
    le_antisymm (norm_ringOfIntegers_le_one j d) (not_lt.mp d.2)
  have := congrArg (fun y => ‖j y‖) hnd
  simp only [map_mul, norm_mul, hd, mul_one] at this
  rw [this]
  exact norm_ringOfIntegers_le_one j n

theorem norm_lt_one_of_valuation_lt_one {x : K}
    (hx : (densePrime j hj).valuation K x < 1) : ‖j x‖ < 1 := by
  obtain ⟨n, d, hnd⟩ := (densePrime j hj).exists_primeCompl_mul_eq_of_integer x hx.le
  have hd : ‖j (algebraMap (𝓞 K) K d)‖ = 1 :=
    le_antisymm (norm_ringOfIntegers_le_one j d) (not_lt.mp d.2)
  have hvd : (densePrime j hj).valuation K (algebraMap (𝓞 K) K d) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
    exact d.2
  have hvn : (densePrime j hj).valuation K (algebraMap (𝓞 K) K n) < 1 := by
    rw [← hnd, map_mul, hvd, mul_one]
    exact hx
  rw [HeightOneSpectrum.valuation_lt_one_iff_mem, mem_densePrime] at hvn
  have := congrArg (fun y => ‖j y‖) hnd
  simp only [map_mul, norm_mul, hd, mul_one] at this
  rw [this]
  exact hvn

theorem valuation_le_one_iff (x : K) :
    (densePrime j hj).valuation K x ≤ 1 ↔ ‖j x‖ ≤ 1 := by
  refine ⟨norm_le_one_of_valuation_le_one j hj, fun h => ?_⟩
  by_contra hv
  push Not at hv
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hv
  have hinv : (densePrime j hj).valuation K x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hv
  have := norm_lt_one_of_valuation_lt_one j hj hinv
  rw [map_inv₀, norm_inv] at this
  have hpos : 0 < ‖j x‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr hx0)
  rw [inv_lt_one₀ hpos] at this
  exact absurd h (not_le.mpr this)

theorem valuation_lt_one_iff (x : K) :
    (densePrime j hj).valuation K x < 1 ↔ ‖j x‖ < 1 := by
  refine ⟨norm_lt_one_of_valuation_lt_one j hj, fun h => ?_⟩
  by_contra hv
  push Not at hv
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hv
  have hinv : (densePrime j hj).valuation K x⁻¹ ≤ 1 := by
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ hv
  have := norm_le_one_of_valuation_le_one j hj hinv
  rw [map_inv₀, norm_inv] at this
  have hpos : 0 < ‖j x‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr hx0)
  rw [inv_le_one₀ hpos] at this
  exact absurd h (not_lt.mpr this)

theorem valuation_lt_iff (x y : K) :
    (densePrime j hj).valuation K x < (densePrime j hj).valuation K y ↔ ‖j x‖ < ‖j y‖ := by
  by_cases hy : y = 0
  · subst hy
    simp
  have hvy : (densePrime j hj).valuation K y ≠ 0 := by simpa using hy
  have hjy : 0 < ‖j y‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr hy)
  have h := valuation_lt_one_iff j hj (x / y)
  rw [map_div₀, map_div₀, norm_div, div_lt_one₀ (zero_lt_iff.mpr hvy), div_lt_one hjy] at h
  exact h

end Comparison

omit [NumberField K] [IsUltrametricDist F] in
/-- A ring embedding into a normed field whose norm order agrees with a valuation is
uniformly inducing for the valuation uniformity. -/
theorem isUniformInducing_of_lt_iff {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation K Γ₀) (j : K →+* F)
    (hw : ∀ x y : K, w x < w y ↔ ‖j x‖ < ‖j y‖)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ x : K, x ≠ 0 ∧ ‖j x‖ < ε) :
    IsUniformInducing (j.comp (WithVal.equiv w).toRingHom) := by
  rw [Filter.HasBasis.isUniformInducing_iff (Valued.hasBasis_uniformity _ _)
    Metric.uniformity_basis_dist]
  constructor
  · intro ε hε
    obtain ⟨x, hx0, hx⟩ := hsmall ε hε
    refine ⟨Units.mk0 (Valued.v.restrict (WithVal.toVal w x)) ?_, trivial, ?_⟩
    · rw [Ne, Valuation.restrict_eq_zero_iff, WithVal.valued_toVal]
      simpa using hx0
    · intro a b hab
      simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff,
        ← WithVal.apply_ofVal, WithVal.ofVal_sub] at hab
      rw [hw, map_sub] at hab
      simp only [Set.mem_ofPred_eq, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe, Function.comp_apply, WithVal.equiv_apply, dist_eq_norm]
      rw [norm_sub_rev]
      exact hab.trans hx
  · intro γ _
    obtain ⟨r, s, hr, hs, hrs⟩ := Valuation.exists_div_eq_of_unit _ γ
    have hr0 : j r.ofVal ≠ 0 := by
      rw [map_ne_zero, Ne, WithVal.ofVal_eq_zero]
      rintro rfl
      simp at hr
    have hs0 : j s.ofVal ≠ 0 := by
      rw [map_ne_zero, Ne, WithVal.ofVal_eq_zero]
      rintro rfl
      simp at hs
    have hjs : 0 < ‖j s.ofVal‖ := norm_pos_iff.mpr hs0
    refine ⟨‖j r.ofVal‖ / ‖j s.ofVal‖, div_pos (norm_pos_iff.mpr hr0) hjs, ?_⟩
    intro a b hab
    simp only [Set.mem_ofPred_eq, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, Function.comp_apply, WithVal.equiv_apply, dist_eq_norm] at hab
    rw [lt_div_iff₀ hjs, norm_sub_rev, ← map_sub, ← norm_mul, ← map_mul, ← hw] at hab
    simp only [Set.mem_ofPred_eq]
    rw [← hrs, lt_div_iff₀ ((Valuation.restrict_pos_iff _ s).mpr hs), ← map_mul,
      Valuation.restrict_lt_iff, ← WithVal.apply_ofVal, ← WithVal.apply_ofVal]
    simpa using hab

variable [CompleteSpace F]

omit [NumberField K] [IsUltrametricDist F] in
/-- `F` as an abstract completion of `K` for a valuation inducing its uniformity. -/
noncomputable def completionPackage {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation K Γ₀) (j : K →+* F) (hj : DenseRange j)
    (hu : IsUniformInducing (j.comp (WithVal.equiv w).toRingHom)) :
    AbstractCompletion (WithVal w) where
  space := F
  coe := j.comp (WithVal.equiv w).toRingHom
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := hu
  dense := by
    have h : Set.range (j.comp (WithVal.equiv w).toRingHom) = Set.range j :=
      (WithVal.equiv w).surjective.range_comp j
    show Dense (Set.range _)
    rw [h]
    exact hj

attribute [local instance] AbstractCompletion.uniformStruct AbstractCompletion.complete
  AbstractCompletion.separation

omit [NumberField K] [IsUltrametricDist F] in
/-- The completion of `K` at a valuation inducing the uniformity of a dense embedding
`j : K →+* F` into a complete field is isomorphic to `F`. -/
noncomputable def completionRingEquiv {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation K Γ₀) (j : K →+* F) (hj : DenseRange j)
    (hu : IsUniformInducing (j.comp (WithVal.equiv w).toRingHom)) :
    w.Completion ≃+* F :=
  { (Completion.cPkg.compareEquiv (completionPackage w j hj hu)).toEquiv with
    map_mul' := (Completion.extensionHom _ hu.uniformContinuous.continuous).map_mul
    map_add' := (Completion.extensionHom _ hu.uniformContinuous.continuous).map_add }

omit [NumberField K] [IsUltrametricDist F] in
theorem continuous_completionRingEquiv {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation K Γ₀) (j : K →+* F) (hj : DenseRange j)
    (hu : IsUniformInducing (j.comp (WithVal.equiv w).toRingHom)) :
    Continuous (completionRingEquiv w j hj hu) :=
  (Completion.cPkg.uniformContinuous_compareEquiv (completionPackage w j hj hu)).continuous

omit [NumberField K] [IsUltrametricDist F] in
theorem continuous_completionRingEquiv_symm {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation K Γ₀) (j : K →+* F) (hj : DenseRange j)
    (hu : IsUniformInducing (j.comp (WithVal.equiv w).toRingHom)) :
    Continuous (completionRingEquiv w j hj hu).symm :=
  (Completion.cPkg.uniformContinuous_compareEquiv_symm (completionPackage w j hj hu)).continuous

omit [NumberField K] [IsUltrametricDist F] in
theorem completionRingEquiv_coe {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation K Γ₀) (j : K →+* F) (hj : DenseRange j)
    (hu : IsUniformInducing (j.comp (WithVal.equiv w).toRingHom)) (x : WithVal w) :
    completionRingEquiv w j hj hu (x : w.Completion) = j (WithVal.equiv w x) :=
  Completion.cPkg.compare_coe (completionPackage w j hj hu) x

/-- A dense ring embedding of a number field into a complete nonarchimedean nontrivially
normed field identifies the field with the adic completion at the prime of integers of
norm less than one, by a ring isomorphism that is continuous in both directions and
extends the embedding. -/
theorem exists_adicCompletion_ringEquiv (j : K →+* F) (hj : DenseRange j) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (φ : v.adicCompletion K ≃+* F),
      (∀ a : 𝓞 K, a ∈ v.asIdeal ↔ ‖j a‖ < 1) ∧ Continuous φ ∧ Continuous φ.symm ∧
      ∀ x : K, φ (algebraMap K (v.adicCompletion K) x) = j x := by
  let v := densePrime j hj
  have hu := isUniformInducing_of_lt_iff (v.valuation K) j (valuation_lt_iff j hj)
    (fun ε hε => exists_ne_zero_norm_lt j hj hε)
  let e := completionRingEquiv (v.valuation K) j hj hu
  refine ⟨v, (HeightOneSpectrum.adicCompletion.equiv K v).trans e, mem_densePrime j hj, ?_, ?_,
    fun x => ?_⟩
  · exact (continuous_completionRingEquiv _ j hj hu).comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion K v)
  · exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v).comp
      (continuous_completionRingEquiv_symm _ j hj hu)
  · exact completionRingEquiv_coe (v.valuation K) j hj hu _

end Langlands.Global.FieldRealization
