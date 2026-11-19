import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCartanIwasawaWeightComparisonOfBasisStatement

/-! # The Cartan–Iwasawa weight comparison by subgroup indices -/

noncomputable section

universe u

open MeasureTheory
open scoped CategoryTheory.MonObj ENNReal NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily

namespace Langlands.HarishChandraSchwartz

/-- The inverse Haar modulus on a closed normalized subgroup is bounded above by
the double-coset index of the normalizing element in the ambient group. -/
private theorem inv_closedNormalizerCharacter_le_doubleCosetIndex
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    (K : OpenSubgroup H) (hKc : IsCompact (K : Set H))
    (U : Subgroup H) (hUc : IsClosed (U : Set H)) (p : Subgroup.normalizer (U : Set H)) :
    ((HaarModulus.closedNormalizerCharacter U hUc p : ℝ≥0) : ℝ)⁻¹ ≤
      (doubleCosetIndex K.toSubgroup (p : H) : ℝ) := by
  let := hUc.locallyCompactSpace
  let : MeasurableSpace U := borel U
  let : BorelSpace U := ⟨rfl⟩
  let Y : OpenSubgroup U := K.comap U.subtype continuous_subtype_val
  let φ := HaarModulus.normalizerConj U p
  let B := Y.toSubgroup.comap φ.symm.toMonoidHom
  let W := B ⊓ Y.toSubgroup
  have hYc : IsCompact (Y : Set U) :=
    hUc.isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage hKc
  have hBo : IsOpen (B : Set U) := Y.isOpen.preimage φ.symm.continuous
  have hWo : IsOpen (W : Set U) := hBo.inter Y.isOpen
  have hfin := relIndex_ne_zero_of_open_compact W hWo Y.toSubgroup hYc
  let C : TopologicalSpace.PositiveCompacts U :=
    ⟨⟨(Y : Set U), hYc⟩, by simpa only [Y.isOpen.interior_eq] using
      (show (Y : Set U).Nonempty from ⟨1, Y.one_mem⟩)⟩
  let mu := Measure.haarMeasure C
  have hmuY : mu (Y : Set U) = 1 := Measure.haarMeasure_self
  have hpre : φ ⁻¹' (B : Set U) = Y := by
    ext x
    change φ.symm (φ x) ∈ Y ↔ x ∈ Y
    rw [φ.symm_apply_apply]
  have hmuB : mu B = (mulEquivHaarChar φ : ℝ≥0∞) := by
    symm
    simpa only [hpre, hmuY, ENNReal.smul_def, smul_eq_mul, mul_one] using
      mulEquivHaarChar_smul_preimage mu (X := (B : Set U)) φ
  have hrel : W.relIndex Y.toSubgroup = B.relIndex Y.toSubgroup :=
    Subgroup.inf_relIndex_right B Y.toSubgroup
  have hbound : 1 ≤ (B.relIndex Y.toSubgroup : ℝ≥0∞) * (mulEquivHaarChar φ : ℝ≥0∞) := by
    calc 1 = mu (Y : Set U) := hmuY.symm
      _ = (W.relIndex Y.toSubgroup : ℝ≥0∞) * mu W :=
        measure_eq_relIndex_mul mu inf_le_right hWo.measurableSet hfin
      _ ≤ (B.relIndex Y.toSubgroup : ℝ≥0∞) * mu B := by
        rw [hrel]
        exact mul_le_mul_right (measure_mono (show (W : Set U) ⊆ B from inf_le_left)) _
      _ = _ := by rw [hmuB]
  have hboundR := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top) hbound
  simp only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.coe_toReal]
    at hboundR
  have hc : 0 < (mulEquivHaarChar φ : ℝ) := NNReal.coe_pos.mpr (mulEquivHaarChar_pos φ)
  have hB : B = (conjSubgroup (p : H) K.toSubgroup).comap U.subtype := by
    ext x
    change ((φ.symm x : U) : H) ∈ K ↔ (x : H) ∈ conjSubgroup (p : H) K.toSubgroup
    exact mem_conjSubgroup.symm
  have hle : B.relIndex Y.toSubgroup ≤ doubleCosetIndex K.toSubgroup (p : H) := by
    rw [hB, Subgroup.relIndex_comap, doubleCosetIndex]
    exact Subgroup.relIndex_le_of_le_right (Subgroup.map_comap_le _ _)
      (doubleCosetIndex_ne_zero_of_compact_open K hKc p)
  change (mulEquivHaarChar φ : ℝ)⁻¹ ≤ _
  exact ((inv_le_iff_one_le_mul₀ hc).mpr hboundR).trans (by exact_mod_cast hle)

private theorem doubleCosetIndex_mul_right_of_mem {H : Type u} [Group H]
    (K : Subgroup H) (p : H) {k : H} (hk : k ∈ K) :
    doubleCosetIndex K (p * k) = doubleCosetIndex K p := by
  have hconj : conjSubgroup (p * k) K = conjSubgroup p K := by
    ext g
    rw [mem_conjSubgroup, mem_conjSubgroup,
      show (p * k)⁻¹ * g * (p * k) = k⁻¹ * (p⁻¹ * g * p) * k by group]
    exact (Subgroup.mem_normalizer_iff''.mp (K.le_normalizer hk) _).symm
  simp only [doubleCosetIndex, hconj]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- The comparison follows by sandwiching the inverse Iwasawa modulus between
the relative index of the radical and the upper volume bound of the Cartan cell. -/
theorem rationalCartanIwasawaWeightComparisonOfBasis :
    RationalCartanIwasawaWeightComparisonOfBasisStatement.{u} := by
  intro F _ _ _ _ G _ _ S i hi ν K0 hK0o hK0c hbasis F0 K hKo hKc hPK
  let L := K ⊓ K0
  have hLo : IsOpen (L : Set (rationalPoints G)) := hKo.inter hK0o
  let K0open : OpenSubgroup (rationalPoints G) := ⟨K0, hK0o⟩
  have hLc : IsCompact (L : Set (rationalPoints G)) := hKc.inter_right K0open.isClosed
  let C : TopologicalSpace.PositiveCompacts (rationalPoints G) :=
    ⟨⟨(L : Set (rationalPoints G)), hLc⟩, by simpa only [hLo.interior_eq] using
      (show (L : Set (rationalPoints G)).Nonempty from ⟨1, L.one_mem⟩)⟩
  let mu := Measure.haarMeasure C
  have hmuL : mu L = 1 := Measure.haarMeasure_self
  have hLindex := relIndex_ne_zero_of_open_compact L hLo K hKc
  obtain ⟨Nc, hNc⟩ := exists_measure_cell_le_doubleCoset mu hK0o hK0c F0
    (fun f : centralizerPoints i => (f : rationalPoints G))
  obtain ⟨Cv, hCv⟩ := exists_measure_doubleCoset_uniformizerPowers_le hi hK0o hK0c hbasis mu
  let A : ℝ≥0 := (L.relIndex K : ℝ≥0) * Nc * Cv + 1
  have hA : 0 < (A : ℝ) := by dsimp [A]; positivity
  refine ⟨Real.sqrt A, Real.sqrt_pos.2 hA, fun y hy g hg => ?_⟩
  set w := uniformizerPowers i (.ofAdd y)
  have hwP : w ∈ standardParabolicPoints i ν ∅ := by
    simpa only [parabolic, rootSet_empty] using
      levi_le_parabolic i ν ∅ (uniformizerPowers_mem_levi i ν ∅ y)
  have hwT : w ∈ torusPoints i :=
    (mem_torusPoints i _).mpr ⟨CocharacterUniformizer.latticeSection F S (.ofAdd y), rfl⟩
  have hwcomm (f : centralizerPoints i) : (f : rationalPoints G) * w = w * (f : rationalPoints G) :=
    (centralizerPoints_le_pointCentralizer i f.property _ hwT).symm
  have hcell : DoubleCoset.doubleCoset g K0 K0 ⊆ rationalCartanCell i K0 F0 y := by
    obtain ⟨k₁, hk₁, k₂, hk₂, f, hf, hg⟩ := hg
    intro x hx
    obtain ⟨l, hl, r, hr, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
    exact ⟨l * k₁, K0.mul_mem hl hk₁, k₂ * r, K0.mul_mem hk₂ hr, f, hf,
      by rw [hg]; simp only [mul_assoc]⟩
  let δ := rationalMinimalModulus i ν
  let dw : ℝ := (δ ⟨w, hwP⟩ : ℝ≥0)
  have hdw : 0 < dw := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hfinL := doubleCosetIndex_ne_zero_of_compact_open
    (⟨L, hLo⟩ : OpenSubgroup (rationalPoints G)) hLc g
  have hupper : (doubleCosetIndex K g : ℝ≥0∞) ≤ (A : ℝ≥0∞) * ENNReal.ofReal dw⁻¹ := by
    have hcomp := (doubleCosetIndex_le (show L ≤ K from inf_le_left) g hfinL hLindex).2
    have hvolume : (doubleCosetIndex L g : ℝ≥0∞) =
        mu (DoubleCoset.doubleCoset g L L) := by
      rw [measure_doubleCoset mu L hLo.measurableSet g hfinL, hmuL, mul_one]
    calc (doubleCosetIndex K g : ℝ≥0∞)
        ≤ (doubleCosetIndex L g : ℝ≥0∞) * (L.relIndex K : ℝ≥0∞) := by exact_mod_cast hcomp
      _ = (L.relIndex K : ℝ≥0∞) * mu (DoubleCoset.doubleCoset g L L) := by rw [hvolume, mul_comm]
      _ ≤ (L.relIndex K : ℝ≥0∞) * mu (rationalCartanCell i K0 F0 y) :=
        mul_le_mul_right (measure_mono ((doubleCoset_mono inf_le_right g).trans hcell)) _
      _ ≤ (L.relIndex K : ℝ≥0∞) * (Nc * mu (DoubleCoset.doubleCoset w K0 K0)) :=
        mul_le_mul_right (hNc w (fun f _ => hwcomm f)) _
      _ ≤ (L.relIndex K : ℝ≥0∞) * (Nc * (Cv * ENNReal.ofReal dw⁻¹)) := by
        gcongr
        exact hCv y hy hwP
      _ ≤ (A : ℝ≥0∞) * ENNReal.ofReal dw⁻¹ := by
        rw [← mul_assoc, ← mul_assoc]
        gcongr
        simp [A]
  have hupperR := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hupper
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hdw.le)] at hupperR
  let p := iwasawaFactor hPK g
  let dp : ℝ := (δ p : ℝ≥0)
  have hdp : 0 < dp := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  obtain ⟨k, hk, hfac⟩ := exists_iwasawaFactor hPK g
  change g = (p : rationalPoints G) * k at hfac
  have hlower : dp⁻¹ ≤ (doubleCosetIndex K g : ℝ) := by
    rw [hfac, doubleCosetIndex_mul_right_of_mem K _ hk]
    let U := standardUnipotentPoints i ν ∅
    exact inv_closedNormalizerCharacter_le_doubleCosetIndex ⟨K, hKo⟩ hKc U
      (isClosed_standardUnipotentPoints i ν ∅)
      ⟨p, standardParabolicPoints_le_normalizer_standardUnipotentPoints i ν ∅ p.2⟩
  have hmod : dw ≤ (A : ℝ) * dp := by
    have hm := (inv_le_iff_one_le_mul₀ hdp).mp (hlower.trans hupperR)
    rw [mul_right_comm (A : ℝ), le_mul_inv_iff₀ hdw, one_mul] at hm
    exact hm
  have hwWeight : iwasawaWeight hPK δ w = Real.sqrt dw := by
    simpa only [mul_one, Real.coe_sqrt] using
      iwasawaWeight_mul (hPK := hPK) (rationalMinimalModulus_eq_one i ν hKo hKc)
        hwP K.one_mem
  have hgWeight : iwasawaWeight hPK δ g = Real.sqrt dp := Real.coe_sqrt
  change iwasawaWeight hPK δ w ≤ Real.sqrt A * iwasawaWeight hPK δ g
  rw [hwWeight, hgWeight, ← Real.sqrt_mul hA.le]
  exact Real.sqrt_le_sqrt hmod

end Langlands.HarishChandraSchwartz
