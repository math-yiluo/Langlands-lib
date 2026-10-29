import Langlands.Representation.Geometric.IntersectionUnipotentHaarStatement
import Langlands.Representation.Geometric.RefinedUnipotentHaarProof

/-! The Haar law on the literal ambient intersection by canonical coordinate transport. -/

open scoped NNReal ENNReal
open MeasureTheory MeasureTheory.Measure

namespace Langlands.Geometric

universe uF

theorem padicIntersectionUnipotentHaarModulus :
    PadicIntersectionUnipotentHaarModulus.{uF} := by
  intro p hp F T n B C w S hS
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  let := T.intersectionUnipotentLocallyCompactSpace B C w S hS
  let M := B.leviSubgroup F.Carrier
  let N := C.leviSubgroup F.Carrier
  let V := C.unipotentSubgroup F.Carrier
  let g := GeneralLinear.permutation n F.Carrier w
  let U := intersectionSource M V g
  let ι := General.intersectionToCorrectionNormalizer M N M V g M.le_normalizer
    (C.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
  let eL := refinedLeviIntersectionEquiv F.Carrier B C w S hS
  let eU := refinedUnipotentIntersectionEquiv F.Carrier B C w S hS
  let := T.leviTopologicalGroup B
  let := T.refinedUnipotentLocallyCompactSpace B S
  have hmeasure : ∀ (m : General.intersectionIn M N g)
      [MeasurableSpace U] [BorelSpace U] (μ : Measure U) [μ.IsHaarMeasure],
      μ.map (HaarModulus.normalizerConj U (ι m)) =
        ((T.refinedLeviModulus B S (eL.symm m) : ℝ≥0)⁻¹) • μ := by
    intro m mU bU μ hμ
    obtain rfl := bU.measurable_eq
    let : MeasurableSpace U := borel _
    have : BorelSpace U := ⟨rfl⟩
    let : MeasurableSpace (refinedUnipotent F.Carrier B S) := borel _
    have : BorelSpace (refinedUnipotent F.Carrier B S) := ⟨rfl⟩
    let ν := μ.map eU.symm
    have : ν.IsHaarMeasure := eU.symm.isHaarMeasure_map μ
    let a := HaarModulus.normalizerConj U (ι m)
    let b := HaarModulus.normalizerConj (refinedUnipotent F.Carrier B S)
      (refinedLeviNormalizer F.Carrier B S (eL.symm m))
    have ha : Measurable a := a.continuous.measurable
    have hb : Measurable b := b.continuous.measurable
    have he : Measurable eU := eU.continuous.measurable
    have he' : Measurable eU.symm := eU.symm.continuous.measurable
    have hν := (padicRefinedUnipotentHaarModulus p F T n B S).1 (eL.symm m) ν
    have hcoord : a ∘ eU = eU ∘ b := by
      funext u
      have h := refinedUnipotentIntersectionEquiv_normalizerConj
        F.Carrier B C w S hS (eL.symm m) u
      simpa only [a, b, eU, eL, Function.comp_apply,
        ContinuousMulEquiv.apply_symm_apply] using h.symm
    have hμ : ν.map eU = μ := by
      change (μ.map eU.symm).map eU = μ
      rw [Measure.map_map he he']
      simp only [Function.comp_def, ContinuousMulEquiv.apply_symm_apply,
        Measure.map_id']
    calc
      μ.map a = (ν.map eU).map a := by rw [hμ]
      _ = (ν.map b).map eU := by
        rw [Measure.map_map ha he, hcoord, ← Measure.map_map he hb]
      _ = ((T.refinedLeviModulus B S (eL.symm m) : ℝ≥0)⁻¹) • ν.map eU := by
        rw [hν, Measure.map_smul _ he.aemeasurable]
      _ = ((T.refinedLeviModulus B S (eL.symm m) : ℝ≥0)⁻¹) • μ := by rw [hμ]
  refine ⟨hmeasure, ?_⟩
  apply MonoidHom.ext
  intro m
  apply Units.ext
  let : MeasurableSpace U := borel _
  have : BorelSpace U := ⟨rfl⟩
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts U) := inferInstance
  let μ : Measure U := haarMeasure K₀
  have h := HaarModulus.normalizerCharacter_smul_map U (ι (eL m)) μ
  rw [hmeasure (eL m) μ, ContinuousMulEquiv.symm_apply_apply, smul_smul] at h
  have hK := congrArg (fun ν : Measure U => ν (K₀ : Set U)) h
  simp only [Measure.smul_apply, μ, haarMeasure_self, ENNReal.smul_def, smul_eq_mul,
    mul_one] at hK
  have h1 : (HaarModulus.normalizerCharacter U (ι (eL m)) : ℝ≥0) *
      (T.refinedLeviModulus B S m : ℝ≥0)⁻¹ = 1 := by
    exact_mod_cast hK
  exact (mul_inv_eq_one₀ (T.refinedLeviModulus B S m).ne_zero).mp h1

end Langlands.Geometric
