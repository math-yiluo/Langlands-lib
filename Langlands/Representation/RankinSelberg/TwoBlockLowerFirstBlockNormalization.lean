import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockMeasures
import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientCoordinates

/-!
# Integral normalization of the lower mixed Haar

The actual lower mixed integral subgroup has normalized mass one. The product
formed from any supplied rectangular Haar has mass equal to its integral cube.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient

open MeasureTheory GeneralLinear QuotientIntegration TopologicalSpace
  TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient TwoBlockUnipotentQuotient
  TwoBlockUnipotentQuotientIntegration
open scoped ENNReal

universe uF uK

section Algebra

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {K : Type uK} [Field K] (O : Subring K)

private theorem matrix_mul_entries_integral {a b c : ℕ}
    {A : Matrix (Fin a) (Fin b) K} {B : Matrix (Fin b) (Fin c) K}
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) :
    ∀ i j, (A * B) i j ∈ O := by
  intro i j
  change ∑ k, A i k * B k j ∈ O
  exact O.sum_mem fun k _ => O.mul_mem (hA i k) (hB k j)

private theorem lowerProduct_entries_integral
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) K)
    (a : GeneralLinear (m 0 + 1) K) (n : GeneralLinear (m 1 + 1) K)
    (hZ : ∀ i j, Z i j ∈ O) (ha : ∀ i j, a i j ∈ O) (hn : ∀ i j, n i j ∈ O) :
    ∀ i j, lowerProduct h K Z a n i j ∈ O := by
  apply forall_index h (fun i j => lowerProduct h K Z a n i j ∈ O)
  · intro i j
    change entryBlock h K (lowerProduct h K Z a n) 0 0 i j ∈ O
    simpa only [entryBlock_lowerProduct_zero_zero] using ha i j
  · intro i j
    change entryBlock h K (lowerProduct h K Z a n) 0 1 i j ∈ O
    simp only [entryBlock_lowerProduct_zero_one, Matrix.zero_apply, O.zero_mem]
  · intro i j
    change entryBlock h K (lowerProduct h K Z a n) 1 0 i j ∈ O
    simpa only [entryBlock_lowerProduct_one_zero] using matrix_mul_entries_integral O hZ ha i j
  · intro i j
    change entryBlock h K (lowerProduct h K Z a n) 1 1 i j ∈ O
    simpa only [entryBlock_lowerProduct_one_one] using hn i j

/-- Integral lower-product coordinates are exactly the integral rectangle and
integral invertible diagonal blocks. -/
theorem lowerProduct_mem_integralSubgroup_iff
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) K)
    (a : GeneralLinear (m 0 + 1) K) (n : GeneralLinear (m 1 + 1) K) :
    lowerProduct h K Z a n ∈ Conductor.integralSubgroup O t ↔
      (∀ i j, Z i j ∈ O) ∧ a ∈ Conductor.integralSubgroup O (m 0) ∧
        n ∈ Conductor.integralSubgroup O (m 1) := by
  rw [Conductor.mem_integralSubgroup, Conductor.mem_integralSubgroup,
    Conductor.mem_integralSubgroup]
  constructor
  · rintro ⟨hg, hgi⟩
    have ha : ∀ i j, a i j ∈ O := by
      intro i j
      have hh := hg ((succBlockShape m h).index 0 i) ((succBlockShape m h).index 0 j)
      change entryBlock h K (lowerProduct h K Z a n) 0 0 i j ∈ O at hh
      simpa only [entryBlock_lowerProduct_zero_zero] using hh
    have hn : ∀ i j, n i j ∈ O := by
      intro i j
      have hh := hg ((succBlockShape m h).index 1 i) ((succBlockShape m h).index 1 j)
      change entryBlock h K (lowerProduct h K Z a n) 1 1 i j ∈ O at hh
      simpa only [entryBlock_lowerProduct_one_one] using hh
    rw [lowerProduct_inv] at hgi
    have hai : ∀ i j, a⁻¹ i j ∈ O := by
      intro i j
      have hh := hgi ((succBlockShape m h).index 0 i) ((succBlockShape m h).index 0 j)
      change entryBlock h K (lowerProduct h K _ a⁻¹ n⁻¹) 0 0 i j ∈ O at hh
      simpa only [entryBlock_lowerProduct_zero_zero] using hh
    have hni : ∀ i j, n⁻¹ i j ∈ O := by
      intro i j
      have hh := hgi ((succBlockShape m h).index 1 i) ((succBlockShape m h).index 1 j)
      change entryBlock h K (lowerProduct h K _ a⁻¹ n⁻¹) 1 1 i j ∈ O at hh
      simpa only [entryBlock_lowerProduct_one_one] using hh
    refine ⟨?_, ⟨ha, hai⟩, ⟨hn, hni⟩⟩
    have hZa : ∀ i j, (Z * a.val) i j ∈ O := by
      intro i j
      have hh := hg ((succBlockShape m h).index 1 i) ((succBlockShape m h).index 0 j)
      change entryBlock h K (lowerProduct h K Z a n) 1 0 i j ∈ O at hh
      simpa only [entryBlock_lowerProduct_one_zero] using hh
    have hh := matrix_mul_entries_integral O hZa hai
    simpa only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using hh
  · rintro ⟨hZ, ⟨ha, hai⟩, ⟨hn, hni⟩⟩
    refine ⟨lowerProduct_entries_integral h O Z a n hZ ha hn, ?_⟩
    rw [lowerProduct_inv]
    exact lowerProduct_entries_integral h O _ _ _
      (matrix_mul_entries_integral O
        (matrix_mul_entries_integral O (fun i j => O.neg_mem (hni i j)) hZ) ha) hai hni

end Algebra

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance lowerNormalizationInstance01 : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance lowerNormalizationInstance02 : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance lowerNormalizationInstance03 : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance lowerNormalizationInstance04 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance lowerNormalizationInstance05 : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance lowerNormalizationInstance06 : MeasurableSpace F.Carrier := borel _
local instance lowerNormalizationInstance07 : BorelSpace F.Carrier := ⟨rfl⟩
local instance lowerNormalizationInstance08 (a b : ℕ) : LocallyCompactSpace (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (LocallyCompactSpace (Fin b → Fin a → F.Carrier))
local instance lowerNormalizationInstance09 (a b : ℕ) : SecondCountableTopology (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin b → Fin a → F.Carrier))
local instance lowerNormalizationInstance10 (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n
local instance lowerNormalizationInstance11 (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance lowerNormalizationInstance12 (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance lowerNormalizationInstance13 (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance lowerNormalizationInstance14 (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance lowerNormalizationInstance15 (n : ℕ) : MeasurableSpace (normOneSubgroup F n) := borel _
local instance lowerNormalizationInstance16 (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance lowerNormalizationInstance17 (n : ℕ) : SecondCountableTopology (normOneSubgroup F n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerNormalizationInstance18 (n : ℕ) : LocallyCompactSpace (normOneSubgroup F n) :=
  (isOpenEmbedding_normOneSubtype F n).locallyCompactSpace
local instance lowerNormalizationInstance19 (n : ℕ) : MeasurableSpace (upperUnipotent n F.Carrier) := borel _
local instance lowerNormalizationInstance20 (n : ℕ) : BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
local instance lowerNormalizationInstance21 (n : ℕ) : SecondCountableTopology (upperUnipotent n F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerNormalizationInstance22 (n : ℕ) : LocallyCompactSpace (upperUnipotent n F.Carrier) :=
  UpperUnipotent.locallyCompactSpace
local instance lowerNormalizationInstance23 : MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance lowerNormalizationInstance24 : BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance lowerNormalizationInstance25 : SecondCountableTopology (lowerMixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerNormalizationInstance26 : LocallyCompactSpace (lowerMixedSubgroup F h) :=
  (isClosed_lowerMixedSubgroup F h).locallyCompactSpace

local notation "R" => Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier
local notation "D" => normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier
local notation "O" => Valuation.integer (ValuativeRel.valuation F.Carrier)

/-- Actual integral points in the lower mixed subgroup, as a compact open subgroup. -/
def lowerMixedIntegralOpen : OpenSubgroup (lowerMixedSubgroup F h) :=
  OpenSubgroup.comap (lowerMixedSubgroup F h).subtype continuous_subtype_val
    (Conductor.levelOpenSubgroup F.Carrier t 0)

theorem lowerMixedIntegralOpen_isCompact :
    IsCompact (lowerMixedIntegralOpen F h : Set (lowerMixedSubgroup F h)) :=
  (isClosed_lowerMixedSubgroup F h).isClosedEmbedding_subtypeVal.isCompact_preimage
    (Conductor.isCompact_levelOpenSubgroup F.Carrier t 0)

/-- Haar measure chosen before any rectangular measure and normalized on the
actual integral points. -/
def lowerMixedHaar : Measure (lowerMixedSubgroup F h) :=
  normalizedCompactOpenHaar (lowerMixedIntegralOpen F h) (lowerMixedIntegralOpen_isCompact F h)

instance lowerMixedHaar_isHaar : (lowerMixedHaar F h).IsHaarMeasure := by
  unfold lowerMixedHaar
  infer_instance

instance lowerMixedHaar_regular : (lowerMixedHaar F h).Regular := by
  unfold lowerMixedHaar
  infer_instance

@[simp] theorem lowerMixedHaar_integral :
    lowerMixedHaar F h (Subtype.val ⁻¹'
      (Conductor.integralSubgroup O t : Set (GeneralLinear (t + 1) F.Carrier))) = 1 := by
  have he : Subtype.val ⁻¹' (Conductor.integralSubgroup O t : Set _) =
      (lowerMixedIntegralOpen F h : Set (lowerMixedSubgroup F h)) := by
    ext x
    change x.val ∈ Conductor.integralSubgroup O t ↔
      x.val ∈ Conductor.levelSubgroup F.Carrier t 0
    rw [Conductor.levelSubgroup_zero]
  rw [he]
  exact normalizedCompactOpenHaar_self _ _

private theorem integralSubgroup_le_normOne (n : ℕ) :
    Conductor.integralSubgroup O n ≤ normOneSubgroup F (n + 1) := by
  intro g hg
  rw [mem_normOneSubgroup_iff]
  let T := F.canonicalTopologicalData
  obtain ⟨hge, hgi⟩ := (Conductor.mem_integralSubgroup O n g).mp hg
  have hdet : ∀ a : GeneralLinear (n + 1) F.Carrier, (∀ i j, a i j ∈ T.Integers) →
      (GeneralLinear.determinant a : F.Carrier) ∈ T.Integers := by
    intro a ha
    let A : Matrix (Fin (n + 1)) (Fin (n + 1)) T.Integers := fun i j => ⟨a i j, ha i j⟩
    have he : T.Integers.subtype.mapMatrix A = a.val := by ext i j; rfl
    have hd : (GeneralLinear.determinant a : F.Carrier) = T.Integers.subtype A.det := by
      rw [RingHom.map_det, he, Matrix.GeneralLinearGroup.val_det_apply]
    rw [hd]
    exact A.det.property
  have h1 := (T.normalizedAbs_le_one_iff_mem_integers _).mpr (hdet g hge)
  have h2 := (T.normalizedAbs_le_one_iff_mem_integers _).mpr (hdet g⁻¹ hgi)
  have hp : T.normalizedAbs (GeneralLinear.determinant g : F.Carrier) *
      T.normalizedAbs (GeneralLinear.determinant g⁻¹ : F.Carrier) = 1 := by
    rw [← T.normalizedAbs_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, T.normalizedAbs_one]
  have hn := T.normalizedAbs_nonneg (GeneralLinear.determinant g : F.Carrier)
  have hni := T.normalizedAbs_nonneg (GeneralLinear.determinant g⁻¹ : F.Carrier)
  have hv : T.normalizedAbs (GeneralLinear.determinant g : F.Carrier) = 1 := by nlinarith
  apply Units.ext
  apply NNReal.eq
  rw [T.determinantNorm_coe]
  simpa using hv

/-- The restriction-normalized norm-one Haar gives its integral subgroup mass one. -/
theorem normOneHaar_integral (n : ℕ) :
    normOneHaar F n (Subtype.val ⁻¹'
      (Conductor.integralSubgroup O n : Set (GeneralLinear (n + 1) F.Carrier))) = 1 := by
  have hK : MeasurableSet (Conductor.integralSubgroup O n : Set (GeneralLinear (n + 1) F.Carrier)) :=
    (Conductor.isOpen_integralSubgroup O n F.canonicalTopologicalData.isOpen_integers).measurableSet
  have he := congrArg (fun μ : Measure (GeneralLinear (n + 1) F.Carrier) =>
      μ (Conductor.integralSubgroup O n : Set _)) (map_normOneHaar F n)
  rw [Measure.map_apply (isOpenEmbedding_normOneSubtype F (n + 1)).continuous.measurable hK,
    Measure.restrict_apply hK] at he
  have hs : (Conductor.integralSubgroup O n : Set (GeneralLinear (n + 1) F.Carrier)) ∩
      (normOneSubgroup F (n + 1) : Set _) = Conductor.integralSubgroup O n :=
    Set.inter_eq_left.mpr (integralSubgroup_le_normOne F n)
  rwa [hs, generalLinearHaar_integralSubgroup] at he

/-- Integral points in the actual coordinates form the three expected integral sets. -/
theorem lowerMixed_preimage_integral :
    lowerMixedSubgroupHomeomorph F h ⁻¹'
      (lowerMixedIntegralOpen F h : Set (lowerMixedSubgroup F h)) =
      {Z : R | ∀ i j, Z i j ∈ O} ×ˢ
        ((Subtype.val ⁻¹' (Conductor.integralSubgroup O (m 0) : Set _)) ×ˢ
          (unipotentIntegralOpen F.Carrier (m 1) : Set _)) := by
  ext ⟨Z, a, n⟩
  change lowerProduct h F.Carrier Z a.val n.val ∈ Conductor.levelSubgroup F.Carrier t 0 ↔ _
  rw [Conductor.levelSubgroup_zero, lowerProduct_mem_integralSubgroup_iff]
  change _ ↔ (∀ i j, Z i j ∈ O) ∧ a.val ∈ Conductor.integralSubgroup O (m 0) ∧
    n.val ∈ Conductor.levelSubgroup F.Carrier (m 1) 0
  rw [Conductor.levelSubgroup_zero]

/-- The coefficient of the coordinate product is the supplied integral-cube mass. -/
theorem lowerMixedProductMeasure_eq_smul
    (μR : Measure R) [μR.IsAddHaarMeasure] :
    lowerMixedProductMeasure F h μR = μR {Z | ∀ i j, Z i j ∈ O} • lowerMixedHaar F h := by
  have key := Measure.isMulLeftInvariant_eq_smul
    (lowerMixedProductMeasure F h μR) (lowerMixedHaar F h)
  have hc := DFunLike.congr_fun key (lowerMixedIntegralOpen F h : Set (lowerMixedSubgroup F h))
  have hK : MeasurableSet (lowerMixedIntegralOpen F h : Set (lowerMixedSubgroup F h)) :=
    (lowerMixedIntegralOpen F h).isOpen.measurableSet
  have h1 : lowerMixedHaar F h (lowerMixedIntegralOpen F h : Set (lowerMixedSubgroup F h)) = 1 :=
    normalizedCompactOpenHaar_self _ _
  change Measure.map (lowerMixedSubgroupHomeomorph F h)
    (μR.prod ((normOneHaar F (m 0)).prod (unipotentHaar F.Carrier (m 1)))) _ = _ at hc
  rw [Measure.map_apply (lowerMixedSubgroupHomeomorph F h).continuous.measurable hK,
    lowerMixed_preimage_integral, Measure.prod_prod, Measure.prod_prod,
    normOneHaar_integral, unipotentHaar_integral, one_mul, mul_one,
    Measure.coe_nnreal_smul_apply, h1, mul_one] at hc
  rw [hc, Measure.coe_nnreal_smul]
  exact key

instance lowerMixedHaar_isMulRightInvariant : (lowerMixedHaar F h).IsMulRightInvariant := by
  have key := Measure.isMulLeftInvariant_eq_smul (lowerMixedHaar F h)
    (lowerMixedProductMeasure F h (Measure.addHaar : Measure R))
  rw [key]
  infer_instance

/-- Compatible quotient existence for the one normalized lower mixed Haar. -/
theorem lowerMixed_compatibleMeasureExists
    [MeasurableSpace (LowerMixedQuotient F h)] [BorelSpace (LowerMixedQuotient F h)] :
    CompatibleMeasureExists (lowerMixedSubgroup F h)
      (generalLinearHaar F.Carrier t) (lowerMixedHaar F h) :=
  Langlands.QuotientIntegration.compatibleMeasureExists (lowerMixedSubgroup F h)
    (isClosed_lowerMixedSubgroup F h) (generalLinearHaar F.Carrier t) (lowerMixedHaar F h)

end Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient
