import Langlands.LocalField.ContinuousIntegerTransport
import Langlands.LocalField.Definitions
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-! # Compatible p-adic data on a supplied relative local field -/

noncomputable section

open Filter ValuativeRel
open scoped Topology

namespace Langlands.LocalField

universe u v

section ValuativeRelation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

private theorem valuation_lt_one_iff_tendsto_pow {K : Type*} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : K) :
    valuation K x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  constructor
  · intro hx
    let := IsTopologicalAddGroup.rightUniformSpace K
    let := isUniformAddGroup_of_addCommGroup (G := K)
    have : MulArchimedean (ValueGroupWithZero K) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    exact Valued.tendsto_zero_pow_of_v_lt_one hx
  · intro h
    have hball : {y : K | valuation K y < 1} ∈ 𝓝 (0 : K) :=
      (IsValuativeTopology.hasBasis_nhds_zero' K).mem_of_mem one_ne_zero
    obtain ⟨n, hn⟩ := (h.eventually hball).exists
    have hn' : valuation K x ^ n < 1 := by simpa only [Set.mem_ofPred_eq, map_pow] using hn
    by_contra! hbad
    exact hn'.not_ge (one_le_pow₀ hbad)

/-- A continuous embedding of nonarchimedean local fields reflects and
preserves the integer ring. -/
theorem mem_integers_map_iff_of_continuous (g : F →+* E) (hg : Continuous g) (x : F) :
    valuation E (g x) ≤ 1 ↔ valuation F x ≤ 1 := by
  constructor
  · intro hx
    by_contra! hv
    have hx0 : x ≠ 0 := by
      intro h
      simp [h] at hv
    have hinv : valuation F x⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hv
    have hp := (hg.tendsto 0).comp ((valuation_lt_one_iff_tendsto_pow _).mp hinv)
    have hginv : valuation E ((g x)⁻¹) < 1 := by
      apply (valuation_lt_one_iff_tendsto_pow _).mpr
      simpa only [Function.comp_def, map_pow, map_inv₀, map_zero] using hp
    rw [map_inv₀] at hginv
    have hpos : 0 < valuation E (g x) :=
      pos_iff_ne_zero.mpr ((map_ne_zero _).mpr ((map_ne_zero _).mpr hx0))
    exact hx.not_gt ((inv_lt_one₀ hpos).mp hginv)
  · exact (LocalFieldData.ofInstances F).map_mem_integers_of_continuous
      (LocalFieldData.ofInstances E) g hg

variable [Algebra F E]

/-- A continuous field algebra map induces the given valuative relation on the base. -/
theorem valuativeExtension_of_continuous (hcont : Continuous (algebraMap F E)) :
    ValuativeExtension F E := by
  refine ⟨fun x y => ?_⟩
  rw [(valuation E).vle_iff_le, (valuation F).vle_iff_le]
  by_cases hy : y = 0
  · simp [hy]
  have hy' : algebraMap F E y ≠ 0 := (map_ne_zero _).mpr hy
  have hpos : 0 < valuation F y := pos_iff_ne_zero.mpr ((map_ne_zero _).mpr hy)
  have hpos' : 0 < valuation E (algebraMap F E y) :=
    pos_iff_ne_zero.mpr ((map_ne_zero _).mpr hy')
  have h := mem_integers_map_iff_of_continuous (algebraMap F E) hcont (x / y)
  simpa only [map_div₀, div_le_one₀ hpos, div_le_one₀ hpos'] using h

end ValuativeRelation

section PadicExtension

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)
  (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F.Carrier E] [Algebra (Padic p) E] [IsScalarTower (Padic p) F.Carrier E]
  [FiniteDimensional F.Carrier E]

/-- A compatible finite extension of a supplied p-adic field, with the
original upper topology and valuation. -/
def suppliedPadicExtension
    (hcont : letI := T.topology; Continuous (algebraMap F.Carrier E)) :
    letI := FiniteDimensional.trans (Padic p) F.Carrier E
    (PadicField.ofField (p := p) E).TopologicalData := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.valuativeExtension
  let := T.moduleTopology
  let := FiniteDimensional.trans (Padic p) F.Carrier E
  let := valuativeExtension_of_continuous hcont
  let : ValuativeExtension (Padic p) E := ⟨fun x y => by
    simp only [IsScalarTower.algebraMap_apply (Padic p) F.Carrier E, ValuativeExtension.vle_iff_vle]⟩
  have hFE : Continuous (algebraMap (Padic p) E) := by
    have h := hcont.comp (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (Padic p) F.Carrier))
    exact (IsScalarTower.algebraMap_eq (Padic p) F.Carrier E).symm ▸ h
  let : ContinuousSMul (Padic p) E := ⟨by
    simp only [Algebra.smul_def]
    exact (hFE.comp continuous_fst).mul continuous_snd⟩
  let := IsTopologicalAddGroup.rightUniformSpace E
  let := isUniformAddGroup_of_addCommGroup (G := E)
  let := HarmonicAnalysis.GeneralLocalField.t2Space E
  let : IsModuleTopology (Padic p) E := isModuleTopologyOfFiniteDimensional
  exact { topology := (inferInstance : TopologicalSpace E)
          valuativeRel := (inferInstance : ValuativeRel E)
          valuativeExtension := (inferInstance : ValuativeExtension (Padic p) E)
          moduleTopology := (inferInstance : IsModuleTopology (Padic p) E)
          localField := (inferInstance : IsNonarchimedeanLocalField E) }

end PadicExtension

end Langlands.LocalField
