import Langlands.Analysis.Local.QuotientFactorization
import Langlands.Analysis.Local.QuotientCompactOpenOrbitProof
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Exact complementary-subgroup Haar normalization from compact open masses -/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure
open scoped CompactlySupported NNReal ENNReal

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H K : Subgroup G) (m : H × K ≃ₜ G)
  (hm : ∀ p : H × K, m p = p.1.val * p.2.val)

/-- The actual complementary-subgroup chart intertwines right multiplication
in the subgroup with the actual quotient's ambient right action. -/
theorem factorQuotientHomeomorph_mul (k l : K) :
    factorQuotientHomeomorph H Subtype.val m hm (k * l) =
      rightTranslate H (l : G) (factorQuotientHomeomorph H Subtype.val m hm k) := rfl

variable [MeasurableSpace K] [BorelSpace K]
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]

/-- The actual quotient measure transported from the complementary subgroup.
Its equality with a compatible Weil measure is proved below from local
compact-open normalization. -/
def factorQuotientMeasure (μK : Measure K) : Measure (LeftQuotient H) :=
  Measure.map (factorQuotientHomeomorph H Subtype.val m hm) μK

include hm in
/-- Right invariance on the actual quotient pulls back to right invariance
on the complementary subgroup, without normality or commutation. -/
theorem isMulRightInvariant_map_factorQuotientHomeomorph_symm
    (ν : Measure (LeftQuotient H))
    (hinv : ∀ g : G, MeasurePreserving (rightTranslate H g) ν ν) :
    IsMulRightInvariant
      (Measure.map (factorQuotientHomeomorph H Subtype.val m hm).symm ν) := by
  let c := factorQuotientHomeomorph H Subtype.val m hm
  constructor
  intro k
  have hcomm : (fun x : K => x * k) ∘ c.symm =
      c.symm ∘ rightTranslate H (k : G) := by
    funext q
    apply c.injective
    change c (c.symm q * k) = c (c.symm (rightTranslate H (k : G) q))
    rw [factorQuotientHomeomorph_mul, Homeomorph.apply_symm_apply,
      Homeomorph.apply_symm_apply]
  rw [Measure.map_map (measurable_mul_const k) c.symm.continuous.measurable,
    hcomm, ← Measure.map_map c.symm.continuous.measurable
      (rightTranslate H (k : G)).continuous.measurable, (hinv (k : G)).map_eq]

section Comparison

variable [T2Space G] [LocallyCompactSpace G]
  (hH : IsClosed (H : Set G))
  (μK : Measure K) [IsHaarMeasure μK] [μK.Regular] [IsMulRightInvariant μK]

omit [T2Space G] in
/-- A regular right-invariant quotient measure pulls back to a scalar
multiple of the supplied regular two-sided Haar measure on the complement. -/
theorem exists_smul_map_factorQuotientHomeomorph_symm
    (ν : Measure (LeftQuotient H)) [ν.Regular]
    (hinv : ∀ g : G, MeasurePreserving (rightTranslate H g) ν ν) :
    ∃ a : ℝ≥0,
      Measure.map (factorQuotientHomeomorph H Subtype.val m hm).symm ν = a • μK := by
  let c := factorQuotientHomeomorph H Subtype.val m hm
  let : LocallyCompactSpace (LeftQuotient H) := leftQuotient_locallyCompactSpace H
  let : LocallyCompactSpace K := c.isClosedEmbedding.locallyCompactSpace
  let M := Measure.map c.symm ν
  have : M.Regular := Measure.Regular.map c.symm
  have : M.IsMulRightInvariant :=
    isMulRightInvariant_map_factorQuotientHomeomorph_symm H K m hm ν hinv
  have : μK.inv.IsHaarMeasure := {
    toIsMulLeftInvariant := inferInstance
    toIsFiniteMeasureOnCompacts := inferInstance
    toIsOpenPosMeasure := inferInstance }
  let a := haarScalarFactor M.inv μK.inv
  have hi : M.inv = a • μK.inv := isMulLeftInvariant_eq_smul_of_regular M.inv μK.inv
  refine ⟨a, ?_⟩
  calc
    M = M.inv.inv := (Measure.inv_inv M).symm
    _ = (a • μK.inv).inv := congrArg Measure.inv hi
    _ = a • μK := by
      rw [Measure.inv_def, Measure.map_smul a measurable_inv.aemeasurable,
        ← Measure.inv_def, Measure.inv_inv]

variable [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace H] [BorelSpace H]
  {μG : Measure G} {μH : Measure H}
  [IsHaarMeasure μG] [μG.Regular]
  [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
  {ν : Measure (LeftQuotient H)}

include hH in
/-- The actual quotient chart is exactly measure preserving when one compact
open quotient orbit has the matching Haar normalization. A full product
measure identity is not assumed. -/
theorem IsCompatible.measurePreserving_factorQuotientHomeomorph_of_compactOpen
    (hν : IsCompatible H μG μH ν)
    (S : OpenSubgroup G) (hS : IsCompact (S : Set G))
    (B : OpenSubgroup K) (hB : IsCompact (B : Set K))
    (horbit : factorQuotientHomeomorph H Subtype.val m hm '' (B : Set K) =
      leftQuotientMap H '' (S : Set G))
    (hnorm : μG (S : Set G) =
      μH {h : H | (h : G) ∈ S} * μK (B : Set K)) :
    MeasurePreserving (factorQuotientHomeomorph H Subtype.val m hm) μK ν := by
  let c := factorQuotientHomeomorph H Subtype.val m hm
  let : T2Space (LeftQuotient H) := leftQuotient_t2Space H hH
  let : ν.Regular := hν.regular
  let A : Set H := {h : H | (h : G) ∈ S}
  have hA : {h : H | (1 : G)⁻¹ * (h : G) * 1 ∈ S} = A := by
    ext h
    simp [A]
  have hAo : IsOpen A := hA ▸ isOpen_compactOpenOrbitStabilizer H S 1
  have hAc : IsCompact A := hA ▸ isCompact_compactOpenOrbitStabilizer H hH S hS 1
  have hapos : 0 < μH A := hAo.measure_pos μH ⟨1, by simp [A]⟩
  have hafin : μH A < ⊤ := hAc.measure_lt_top
  have hCc : IsCompact (leftQuotientMap H '' (S : Set G)) :=
    hS.image (leftQuotient_isOpenQuotientMap H).continuous
  have hmass : μH A * ν (leftQuotientMap H '' (S : Set G)) = μG (S : Set G) := by
    have hi := IsCompatible.integral_compactOpenOrbit H hH μG μH S hS ν hν
      (1 : G) (fun _ => 1) continuous_const
    simp only [inv_one, one_mul, mul_one] at hi
    change (μH A).toReal *
      (∫ _ in leftQuotientMap H '' (S : Set G), (1 : ℝ) ∂ν) =
      ∫ _ in (S : Set G), (1 : ℝ) ∂μG at hi
    have hreal : (μH A).toReal *
        (ν (leftQuotientMap H '' (S : Set G))).toReal = (μG (S : Set G)).toReal := by
      simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ,
        smul_eq_mul, mul_one] using hi
    apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.mul_ne_top hafin.ne hCc.measure_lt_top.ne) hS.measure_lt_top.ne).mp
    simpa only [ENNReal.toReal_mul] using hreal
  have horbitmass : ν (leftQuotientMap H '' (S : Set G)) = μK (B : Set K) := by
    apply (ENNReal.mul_right_inj hapos.ne' hafin.ne).mp
    exact hmass.trans hnorm
  have hpre : c.symm ⁻¹' (B : Set K) = c '' (B : Set K) := by
    ext q
    constructor
    · intro hq
      exact ⟨c.symm q, hq, c.apply_symm_apply q⟩
    · rintro ⟨k, hk, rfl⟩
      simpa using hk
  have hMB : Measure.map c.symm ν (B : Set K) = μK (B : Set K) := by
    rw [Measure.map_apply c.symm.continuous.measurable B.isOpen.measurableSet,
      hpre, horbit, horbitmass]
  obtain ⟨a, ha⟩ := exists_smul_map_factorQuotientHomeomorph_symm H K m hm μK ν
    hν.right_invariant
  have haB : (a : ℝ≥0∞) * μK (B : Set K) = μK (B : Set K) := by
    rw [ha, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hMB
    exact hMB
  have haposK : μK (B : Set K) ≠ 0 := (B.isOpen.measure_pos μK ⟨1, B.one_mem⟩).ne'
  have hafinK : μK (B : Set K) ≠ ⊤ := hB.measure_lt_top.ne
  have ha1 : a = 1 := by
    have he := (ENNReal.mul_eq_right haposK hafinK).mp haB
    exact_mod_cast he
  have hM : Measure.map c.symm ν = μK := by simpa only [ha1, one_smul] using ha
  refine ⟨c.continuous.measurable, ?_⟩
  rw [← hM, Measure.map_map c.continuous.measurable c.symm.continuous.measurable,
    Homeomorph.self_comp_symm, Measure.map_id]

include hH in
/-- The constructed measure agrees with the supplied compatible quotient
measure when their compact-open normalizations agree. -/
theorem IsCompatible.factorQuotientMeasure_eq_of_compactOpen
    (hν : IsCompatible H μG μH ν)
    (S : OpenSubgroup G) (hS : IsCompact (S : Set G))
    (B : OpenSubgroup K) (hB : IsCompact (B : Set K))
    (horbit : factorQuotientHomeomorph H Subtype.val m hm '' (B : Set K) =
      leftQuotientMap H '' (S : Set G))
    (hnorm : μG (S : Set G) =
      μH {h : H | (h : G) ∈ S} * μK (B : Set K)) :
    factorQuotientMeasure H K m hm μK = ν :=
  (hν.measurePreserving_factorQuotientHomeomorph_of_compactOpen H K m hm hH μK
    S hS B hB horbit hnorm).map_eq

section Product

variable [BorelSpace (H × K)] [SFinite μH] [SFinite μK]
  [(μH.prod μK).Regular]

omit hH [μK.Regular] [IsMulRightInvariant μK] [IsHaarMeasure μG] [μH.Regular] in
/-- Conversely, exact quotient normalization implies the exact ambient product
identity, using compact tests, scalar Fubini and the actual Weil formula. -/
theorem IsCompatible.measurePreserving_factorProduct
    (hν : IsCompatible H μG μH ν)
    (hc : MeasurePreserving (factorQuotientHomeomorph H Subtype.val m hm) μK ν) :
    MeasurePreserving m (μH.prod μK) μG := by
  let c := factorQuotientHomeomorph H Subtype.val m hm
  have : (Measure.map m (μH.prod μK)).Regular := Measure.Regular.map m
  refine ⟨m.continuous.measurable, ?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hfi : Integrable (fun p : H × K => f (m p)) (μH.prod μK) :=
    (f.continuous.comp m.continuous).integrable_of_hasCompactSupport
      (f.hasCompactSupport.comp_homeomorph m)
  calc
    (∫ g, f g ∂Measure.map m (μH.prod μK)) =
        ∫ p : H × K, f (m p) ∂μH.prod μK := integral_map_equiv m.toMeasurableEquiv f
    _ = ∫ k, ∫ h : H, f (m (h, k)) ∂μH ∂μK := integral_prod_symm _ hfi
    _ = ∫ k, quotientAverageReal H μH f (c k) ∂μK := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun k => by
        simp only [c, factorQuotientHomeomorph_apply, quotientAverageReal_mk, hm])
    _ = ∫ q, quotientAverageReal H μH f q ∂ν :=
      hc.integral_comp c.toMeasurableEquiv.measurableEmbedding _
    _ = ∫ g, f g ∂μG :=
      hν.integral_quotientAverageReal f f.continuous f.hasCompactSupport

include hH in
/-- One compact-open normalization determines the full product measure
for the literal complementary-subgroup coordinates. -/
theorem IsCompatible.measurePreserving_factorProduct_of_compactOpen
    (hν : IsCompatible H μG μH ν)
    (S : OpenSubgroup G) (hS : IsCompact (S : Set G))
    (B : OpenSubgroup K) (hB : IsCompact (B : Set K))
    (horbit : factorQuotientHomeomorph H Subtype.val m hm '' (B : Set K) =
      leftQuotientMap H '' (S : Set G))
    (hnorm : μG (S : Set G) =
      μH {h : H | (h : G) ∈ S} * μK (B : Set K)) :
    MeasurePreserving m (μH.prod μK) μG :=
  hν.measurePreserving_factorProduct H K m hm μK
    (hν.measurePreserving_factorQuotientHomeomorph_of_compactOpen H K m hm hH μK
      S hS B hB horbit hnorm)

end Product

end Comparison

end Langlands.QuotientIntegration
