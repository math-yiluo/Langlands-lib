import Langlands.Analysis.Local.ModularCharacterRegularityStatement
import Mathlib.GroupTheory.OrderOfElement

noncomputable section

namespace Langlands.Haar

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

universe u

/-- A nonnegative-real character with finite image is trivial. -/
theorem positiveCharacter_eq_one_of_finite_range {G : Type u} [Group G]
    (χ : G →* ℝ≥0) (hχ : (Set.range χ).Finite) (g : G) : χ g = 1 := by
  let φ := χ.toHomUnits
  have hφ : (Set.range φ).Finite := by
    apply (hχ.preimage Units.val_injective.injOn).subset
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  have : Finite φ.range := hφ.to_subtype
  obtain ⟨n, hn, hpow⟩ :=
    (isOfFinOrder_of_finite (φ.rangeRestrict g)).exists_pow_eq_one
  have hval : χ g ^ n = 1 := by
    simpa [φ] using
      congrArg (fun z : φ.range => ((z : ℝ≥0ˣ) : ℝ≥0)) hpow
  exact (pow_eq_one_iff_of_nonneg zero_le hn.ne').mp hval

section Character

variable {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- Regular Haar scaling and cancellation of a compact open subgroup's mass. -/
theorem modularCharacter_eq_one_of_mem_compactOpen (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) {g : G} (hg : g ∈ K) :
    modularCharacter g = 1 := by
  borelize G
  let μ : Measure G := haar
  have : (map (· * g) μ).Regular := Regular.map (Homeomorph.mulRight g)
  have hmap : map (· * g) μ = modularCharacter g • μ := by
    change map (· * g) μ = modularCharacterFun g • μ
    rw [modularCharacterFun_eq_haarScalarFactor μ g]
    exact isMulLeftInvariant_eq_smul_of_regular _ μ
  have hpre : (· * g) ⁻¹' (K : Set G) = K := by
    ext x
    exact K.toSubgroup.mul_mem_cancel_right hg
  have h := congrArg (fun ν : Measure G => ν (K : Set G)) hmap
  rw [map_apply (measurable_mul_const g) K.isOpen.measurableSet, hpre,
    Measure.smul_apply, nnreal_smul_coe_apply] at h
  have hpos : μ (K : Set G) ≠ 0 :=
    K.isOpen.measure_ne_zero μ ⟨1, K.one_mem⟩
  have hfin : μ (K : Set G) ≠ ∞ := hK.measure_ne_top
  have he : ((modularCharacter g : ℝ≥0) : ℝ≥0∞) = 1 :=
    (ENNReal.mul_eq_right hpos hfin).mp h.symm
  exact_mod_cast he

end Character

section Nonarchimedean

variable {G : Type u} [Group G] [TopologicalSpace G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G]

/-- A compact open subgroup lies in the modular-character kernel. -/
theorem isOpen_ker_modularCharacter :
    IsOpen ((modularCharacter (G := G)).ker : Set G) := by
  obtain ⟨K, hK, _⟩ := Langlands.compactOpenSubgroupBasis G Set.univ (by simp)
  apply Subgroup.isOpen_mono (H₁ := K.toSubgroup)
    (H₂ := (modularCharacter (G := G)).ker) ?_ K.isOpen
  intro g hg
  exact modularCharacter_eq_one_of_mem_compactOpen K hK hg

/-- The modular character is constant on cosets of its open kernel. -/
theorem isLocallyConstant_modularCharacter :
    IsLocallyConstant (modularCharacter (G := G)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨(fun y : G => y * x⁻¹) ⁻¹'
      ((modularCharacter (G := G)).ker : Set G),
    isOpen_ker_modularCharacter.preimage (continuous_id.mul continuous_const), ?_, ?_⟩
  · simp
  · intro y hy
    change modularCharacter (y * x⁻¹) = 1 at hy
    apply mul_right_cancel₀ (modularCharacterFun_pos x⁻¹).ne'
    calc
      modularCharacter y * modularCharacter x⁻¹ = 1 := by
        simpa only [map_mul] using hy
      _ = modularCharacter x * modularCharacter x⁻¹ := by
        rw [← map_mul, mul_inv_cancel, map_one]

/-- Local constancy gives continuity without countability hypotheses. -/
theorem continuous_modularCharacter :
    Continuous (modularCharacter (G := G)) :=
  isLocallyConstant_modularCharacter.continuous

/-- Local constancy makes the image of a compact subgroup finite. -/
theorem modularCharacter_eq_one_of_mem_compact (K : Subgroup G)
    (hK : IsCompact (K : Set G)) {g : G} (hg : g ∈ K) :
    modularCharacter g = 1 := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let χ : K →* ℝ≥0 := (modularCharacter (G := G)).comp K.subtype
  have hχ : IsLocallyConstant χ :=
    isLocallyConstant_modularCharacter.comp_continuous continuous_subtype_val
  exact positiveCharacter_eq_one_of_finite_range χ hχ.range_finite ⟨g, hg⟩

end Nonarchimedean

/-- Regularity and compact-subgroup triviality of Mathlib's modular character. -/
theorem modularCharacterRegularity : ModularCharacterRegularityStatement.{u} := by
  intro G _ _ _ _
  exact ⟨isOpen_ker_modularCharacter, isLocallyConstant_modularCharacter,
    continuous_modularCharacter,
    fun K hK g hg => modularCharacter_eq_one_of_mem_compact K hK hg⟩

end Langlands.Haar
