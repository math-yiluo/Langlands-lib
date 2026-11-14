import Langlands.Representation.RankinSelberg.RankOneMatrixIwasawa
import Langlands.AllField.Group.GL.BlockModulusSupplement
import Langlands.AllField.Representation.RankinSelberg.DiagonalUnipotentHaar
import Langlands.AllField.Representation.RankinSelberg.IwasawaTorusPartitionProof
/-!
# Iwasawa integration on `GL_(n+1)` with a rank-one torus coordinate

The normalized Haar measure of `GL_(n+1)` over a canonical `p`-adic field is
recovered from its restriction to `K = GL_(n+1)(O)` and an explicit measure on
`(GL_1 × (Fˣ)ⁿ) × N`, where `N` is the upper unipotent group. A point
`((g, a), u)` maps to `u * diag(det g / ∏ a, a)`. The torus coordinate carries
the inverse modulus `δ⁻¹` as density; with the Library normalizations the
constant of the formula is exactly one.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.AllField.RankinSelberg.RankOneIwasawa
open Langlands.RankinSelberg.RankOneIwasawa hiding continuous_det_units continuous_point continuous_torusCoord continuous_torusModulus continuous_weight det_point glLocallyCompact glOneMeasure glOneMeasure_sigmaFinite glSecondCountable instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceUnitsCarrier instSecondCountableTopologyCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier iwasawaMeasure iwasawaMeasure_point_preimage iwasawaMeasure_sFinite map_iwasawaMeasure_prod map_unfoldedMeasure matrixLocallyCompact measurable_point measurable_unfoldedPoint measurePreserving_shift parameterBase_isMulLeftInvariant parameterMeasure parameterMeasure_eq_prod parameterMeasure_sigmaFinite tailMeasure tailMeasure_sigmaFinite torusModulus torusModulus_apply torusModulus_cons_one torusModulus_eq_one unfoldedMeasure unfoldedPoint unipotentConj_map unipotentLocallyCompact unipotentSecondCountable unitsSecondCountable weight weight_apply weight_glOne weight_split
open Langlands.AllField.RankinSelberg.RankOneIwasawa
open Langlands.RankinSelberg hiding diagonalConj_map singleton_modulus_real
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.GeneralLinear.BlockShape

universe uF

section Algebra


end Algebra

section Valued


open Langlands.Conductor

end Valued

section Measure

open Langlands.Conductor

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance (m : ℕ) : MeasurableSpace (Langlands.GeneralLinear (m + 1) F) := borel _
local instance (m : ℕ) : BorelSpace (Langlands.GeneralLinear (m + 1) F) := ⟨rfl⟩
local instance (m : ℕ) : MeasurableSpace (upperUnipotent (m + 1) F) := borel _
local instance (m : ℕ) : BorelSpace (upperUnipotent (m + 1) F) := ⟨rfl⟩
local instance : MeasurableSpace Fˣ := borel _
local instance : BorelSpace Fˣ := ⟨rfl⟩

local instance matrixLocallyCompact (m : ℕ) :
    LocallyCompactSpace (Matrix (Fin m) (Fin m) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin m → Fin m → F))

local instance glLocallyCompact (m : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear m F) :=
  inferInstance

local instance glSecondCountable (m : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear m F) := by
  have : SecondCountableTopology (Matrix (Fin m) (Fin m) F) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin m → F))
  have : SecondCountableTopology (Matrix (Fin m) (Fin m) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

local instance unipotentSecondCountable (m : ℕ) :
    SecondCountableTopology (upperUnipotent m F) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (upperUnipotent m F : Set (Langlands.GeneralLinear m F))

local instance unipotentLocallyCompact (m : ℕ) :
    LocallyCompactSpace (upperUnipotent m F) :=
  UpperUnipotent.locallyCompactSpace

local instance unitsSecondCountable : SecondCountableTopology Fˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

/-- The root modulus `δ(t) = ∏_{i<j} |t_i / t_j|` of the diagonal torus. -/
def torusModulus (m : ℕ) : (Fin m → Fˣ) →* ℝ≥0ˣ :=
  ((⟨⟩ : LocalFieldData F).leviModulus (singletons m)).comp (singletonLevi F)

theorem torusModulus_apply {m : ℕ} (t : Fin m → Fˣ) :
    torusModulus F m t = ∏ i : Fin m, ∏ j ∈ Finset.univ.filter (fun j => i < j),
      (⟨⟩ : LocalFieldData F).normalizedAbsUnits (t i) /
        (⟨⟩ : LocalFieldData F).normalizedAbsUnits (t j) :=
  (⟨⟩ : LocalFieldData F).leviModulus_singletonLevi t

theorem continuous_torusModulus (m : ℕ) : Continuous (torusModulus F m) := by
  have hc := (⟨⟩ : LocalFieldData F).continuous_normalizedAbsUnits
  simp_rw [funext (torusModulus_apply F (m := m))]
  refine continuous_finsetProd _ fun i _ => continuous_finsetProd _ fun j _ => ?_
  exact (hc.comp (continuous_apply i)).div' (hc.comp (continuous_apply j))

/-- The modulus is one on integral units. -/
theorem torusModulus_eq_one {m : ℕ} (t : Fin m → Fˣ)
    (ht : ∀ i, ValuativeRel.valuation F (t i : F) = 1) :
    torusModulus F m t = 1 := by
  have h1 : ∀ i, (⟨⟩ : LocalFieldData F).normalizedAbsUnits (t i) = 1 := by
    intro i
    apply Units.ext
    apply NNReal.eq
    rw [(⟨⟩ : LocalFieldData F).normalizedAbsUnits_coe, Units.val_one, NNReal.coe_one,
      (⟨⟩ : LocalFieldData F).normalizedAbs_eq_one_iff_discreteValuation]
    change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)
      (ValuativeRel.valuation F (t i : F)) = 1
    rw [ht i, map_one]
  rw [torusModulus_apply]
  simp [h1]

theorem continuous_det_units (m : ℕ) :
    Continuous (fun g : Langlands.GeneralLinear m F =>
      Matrix.GeneralLinearGroup.det g) := by
  apply Units.continuous_iff.2
  constructor
  · have : (Units.val ∘ fun g : Langlands.GeneralLinear m F =>
        Matrix.GeneralLinearGroup.det g) =
        fun g : Langlands.GeneralLinear m F =>
          (g : Matrix (Fin m) (Fin m) F).det :=
      funext fun g => Matrix.GeneralLinearGroup.val_det_apply g
    rw [this]
    exact Units.continuous_val.matrix_det
  · have : (fun g : Langlands.GeneralLinear m F =>
        (((Matrix.GeneralLinearGroup.det g)⁻¹ : Fˣ) : F)) =
        fun g => ((g⁻¹ : Langlands.GeneralLinear m F) :
          Matrix (Fin m) (Fin m) F).det := by
      funext g
      rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact Units.continuous_coe_inv.matrix_det

theorem continuous_torusCoord (n : ℕ) :
    Continuous (torusCoord (E := F) n) := by
  refine continuous_pi fun i => ?_
  induction i using Fin.cases with
  | zero =>
    change Continuous fun b : Langlands.GeneralLinear (0 + 1) F × (Fin n → Fˣ) =>
      Matrix.GeneralLinearGroup.det b.1 * (∏ i, b.2 i)⁻¹
    exact ((continuous_det_units F _).comp continuous_fst).mul
      (continuous_finsetProd _ fun i _ => (continuous_apply i).comp continuous_snd).inv
  | succ i =>
    change Continuous fun b : Langlands.GeneralLinear (0 + 1) F × (Fin n → Fˣ) =>
      b.2 i
    exact (continuous_apply i).comp continuous_snd

/-- The density `ω(b) = δ(D(b))⁻¹` on the parameter group `GL_1 × (Fˣ)ⁿ`. -/
def weight (n : ℕ) :
    Langlands.GeneralLinear (0 + 1) F × (Fin n → Fˣ) →* ℝ≥0 :=
  (Units.coeHom ℝ≥0).comp ((torusModulus F (n + 1)).comp (torusCoord n))⁻¹

theorem weight_apply {n : ℕ} (b : Langlands.GeneralLinear (0 + 1) F × (Fin n → Fˣ)) :
    weight F n b = ((torusModulus F (n + 1) (torusCoord n b))⁻¹ : ℝ≥0ˣ) := rfl

theorem continuous_weight (n : ℕ) : Continuous (weight F n) := by
  change Continuous fun b => (((torusModulus F (n + 1) (torusCoord n b))⁻¹ : ℝ≥0ˣ) : ℝ≥0)
  exact Units.continuous_val.comp
    (((continuous_torusModulus F (n + 1)).comp (continuous_torusCoord F n)).inv)

/-- The parameter measure: Haar measure on `GL_1 × (Fˣ)ⁿ` with density `ω`. -/
def parameterMeasure (n : ℕ) :
    Measure (Langlands.GeneralLinear (0 + 1) F × (Fin n → Fˣ)) :=
  ((generalLinearHaar F 0).prod
      (Measure.pi fun _ : Fin n => localMultiplicativeHaar F)).withDensity
    fun b => (weight F n b : ℝ≥0∞)

/-- The measure on the full parameter space `(GL_1 × (Fˣ)ⁿ) × N`. -/
def iwasawaMeasure (n : ℕ) :
    Measure ((Langlands.GeneralLinear (0 + 1) F × (Fin n → Fˣ)) ×
      upperUnipotent (n + 1) F) :=
  (parameterMeasure F n).prod (unipotentHaar F n)

instance parameterMeasure_sigmaFinite (n : ℕ) : SigmaFinite (parameterMeasure F n) := by
  unfold parameterMeasure
  infer_instance

instance iwasawaMeasure_sFinite (n : ℕ) : SFinite (iwasawaMeasure F n) := by
  unfold iwasawaMeasure
  infer_instance

local instance parameterBase_isMulLeftInvariant (n : ℕ) :
    ((generalLinearHaar F 0).prod
      (Measure.pi fun _ : Fin n => localMultiplicativeHaar F)).IsMulLeftInvariant :=
  Measure.prod.instIsMulLeftInvariant

/-- The modulus of `diag(x, 1, …, 1)` is `|x|ⁿ`. -/
theorem torusModulus_cons_one {n : ℕ} (x : Fˣ) :
    torusModulus F (n + 1) (Fin.cons x 1) =
      (⟨⟩ : LocalFieldData F).normalizedAbsUnits x ^ n := by
  rw [torusModulus_apply]
  simp_rw [Finset.prod_filter]
  rw [Fin.prod_univ_succ]
  have h0 : (∏ j : Fin (n + 1), if (0 : Fin (n + 1)) < j then
      (⟨⟩ : LocalFieldData F).normalizedAbsUnits ((Fin.cons x 1 : Fin (n + 1) → Fˣ) 0) /
        (⟨⟩ : LocalFieldData F).normalizedAbsUnits ((Fin.cons x 1 : Fin (n + 1) → Fˣ) j)
      else 1) = (⟨⟩ : LocalFieldData F).normalizedAbsUnits x ^ n := by
    rw [Fin.prod_univ_succ]
    simp [Fin.succ_pos]
  have h1 : ∀ i : Fin n, (∏ j : Fin (n + 1), if i.succ < j then
      (⟨⟩ : LocalFieldData F).normalizedAbsUnits
        ((Fin.cons x 1 : Fin (n + 1) → Fˣ) i.succ) /
        (⟨⟩ : LocalFieldData F).normalizedAbsUnits ((Fin.cons x 1 : Fin (n + 1) → Fˣ) j)
      else 1) = 1 := by
    intro i
    apply Finset.prod_eq_one
    intro j _
    split_ifs with hij
    · have hj : j ≠ 0 := by
        intro h
        rw [h] at hij
        exact absurd hij (Fin.not_lt_zero _)
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj
      simp
    · rfl
  rw [h0, Finset.prod_eq_one fun i _ => h1 i, mul_one]

/-- The density on the `GL₁` factor alone is `|det g|⁻ⁿ`. -/
theorem weight_glOne {n : ℕ} (g : Langlands.GeneralLinear (0 + 1) F) :
    weight F n (g, 1) =
      (((⟨⟩ : LocalFieldData F).normalizedAbsUnits (Matrix.GeneralLinearGroup.det g) :
        ℝ≥0) ^ n)⁻¹ := by
  have ht : torusCoord n (g, (1 : Fin n → Fˣ)) =
      Fin.cons (Matrix.GeneralLinearGroup.det g) 1 := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ i => simp
  rw [weight_apply, ht, torusModulus_cons_one, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]

/-- The density splits over the `GL₁` and torus factors. -/
theorem weight_split {n : ℕ} (b : Langlands.GeneralLinear (0 + 1) F × (Fin n → Fˣ)) :
    weight F n b = weight F n (b.1, 1) * weight F n (1, b.2) := by
  rw [← map_mul]
  congr 1
  ext <;> simp

/-- The determinant of a parametrization point is the determinant of its `GL₁`
coordinate. -/
theorem det_point {n : ℕ}
    (x : (Langlands.GeneralLinear (0 + 1) F × (Fin n → Fˣ)) ×
      upperUnipotent (n + 1) F) :
    Matrix.GeneralLinearGroup.det (point x) = Matrix.GeneralLinearGroup.det x.1.1 := by
  rw [point, map_mul, det_diagonalUnits, Fin.prod_univ_succ, torusCoord_zero]
  have hu : Matrix.GeneralLinearGroup.det (x.2 : Langlands.GeneralLinear (n + 1) F) = 1 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
      Matrix.det_of_isUpperTriangular x.2.property.1]
    exact Finset.prod_eq_one fun i _ => UpperUnipotent.entry_diag x.2 i
  simp only [torusCoord_succ, hu, one_mul, inv_mul_cancel_right]

/-- Diagonal conjugation scales the normalized unipotent Haar measure by `δ⁻¹`. -/
theorem unipotentConj_map (n : ℕ) (a : Fin (n + 1) → Fˣ) :
    (unipotentHaar F n).map (diagonalConj a) =
      ((torusModulus F (n + 1) a : ℝ≥0)⁻¹) • unipotentHaar F n := by
  exact diagonalConj_map F (⟨⟩ : LocalFieldData F) n a

theorem continuous_point (n : ℕ) :
    Continuous (point (E := F) (n := n)) :=
  (continuous_subtype_val.comp continuous_snd).mul
    (continuous_diagonalUnits'.comp ((continuous_torusCoord F n).comp continuous_fst))

theorem measurable_point (n : ℕ) : Measurable (point (E := F) (n := n)) :=
  (continuous_point F n).measurable

/-- Left translation in parameters preserves the parameter measure. -/
theorem measurePreserving_shift (n : ℕ)
    (x₀ : (Langlands.GeneralLinear (0 + 1) F × (Fin n → Fˣ)) ×
      upperUnipotent (n + 1) F) :
    MeasurePreserving (shift x₀) (iwasawaMeasure F n) (iwasawaMeasure F n) := by
  have hf : Measurable fun b : Langlands.GeneralLinear (0 + 1) F × (Fin n → Fˣ) =>
      x₀.1⁻¹ * b := (continuous_const.mul continuous_id).measurable
  have hg : Measurable fun u : upperUnipotent (n + 1) F =>
      diagonalConj (torusCoord n x₀.1)⁻¹ (x₀.2⁻¹ * u) :=
    ((continuous_diagonalConj _).comp (continuous_const.mul continuous_id)).measurable
  refine ⟨hf.prodMap hg, ?_⟩
  change Measure.map (Prod.map (fun b => x₀.1⁻¹ * b)
    (fun u => diagonalConj (torusCoord n x₀.1)⁻¹ (x₀.2⁻¹ * u)))
      ((parameterMeasure F n).prod (unipotentHaar F n)) = _
  rw [← Measure.map_prod_map _ _ hf hg]
  have h1 : (parameterMeasure F n).map (fun b => x₀.1⁻¹ * b) =
      ((weight F n x₀.1 : ℝ≥0) : ℝ≥0∞) • parameterMeasure F n := by
    have := map_mul_left_withDensity ((generalLinearHaar F 0).prod
      (Measure.pi fun _ : Fin n => localMultiplicativeHaar F)) (weight F n)
      (continuous_weight F n).measurable x₀.1⁻¹
    rw [inv_inv] at this
    exact this
  have h2 : (unipotentHaar F n).map
      (fun u => diagonalConj (torusCoord n x₀.1)⁻¹ (x₀.2⁻¹ * u)) =
      ((torusModulus F (n + 1) (torusCoord n x₀.1)⁻¹ : ℝ≥0)⁻¹) • unipotentHaar F n := by
    have hm : Measurable fun u : upperUnipotent (n + 1) F => x₀.2⁻¹ * u :=
      (continuous_const.mul continuous_id).measurable
    rw [show (fun u => diagonalConj (torusCoord n x₀.1)⁻¹ (x₀.2⁻¹ * u)) =
        (diagonalConj (torusCoord n x₀.1)⁻¹) ∘ fun u => x₀.2⁻¹ * u from rfl,
      ← Measure.map_map (continuous_diagonalConj _).measurable hm,
      map_mul_left_eq_self, unipotentConj_map]
  rw [h1, h2, Measure.prod_smul_left, Measure.prod_smul_right, ENNReal.smul_def, smul_smul]
  have hc : ((weight F n x₀.1 : ℝ≥0) : ℝ≥0∞) *
      (((torusModulus F (n + 1) (torusCoord n x₀.1)⁻¹ : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [← ENNReal.coe_mul, weight_apply, map_inv, Units.val_inv_eq_inv_val, inv_inv,
      inv_mul_cancel₀ (Units.ne_zero _), ENNReal.coe_one]
  rw [hc, one_smul]
  rfl

/-- The integral subgroup has preimage of mass one in the parameter space. -/
theorem iwasawaMeasure_point_preimage (n : ℕ) :
    iwasawaMeasure F n (point ⁻¹'
      (integralSubgroup (ValuativeRel.valuation F).integer n :
        Set (Langlands.GeneralLinear (n + 1) F))) = 1 := by
  set v := ValuativeRel.valuation F
  set S : Set (Langlands.GeneralLinear (0 + 1) F × (Fin n → Fˣ)) :=
    (integralSubgroup v.integer 0 : Set (Langlands.GeneralLinear (0 + 1) F)) ×ˢ
      Set.univ.pi fun _ => (integralUnits v.integer : Set Fˣ) with hS
  have hpre : point ⁻¹' (integralSubgroup v.integer n :
      Set (Langlands.GeneralLinear (n + 1) F)) =
      S ×ˢ (unipotentIntegralOpen F n : Set (upperUnipotent (n + 1) F)) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, Set.mem_prod, Set.mem_univ_pi, hS]
    rw [point_mem_integralSubgroup_iff, torusCoord_valuation_iff]
    have hu : x.2 ∈ unipotentIntegralOpen F n ↔
        (x.2 : Langlands.GeneralLinear (n + 1) F) ∈ integralSubgroup v.integer n := by
      change (x.2 : Langlands.GeneralLinear (n + 1) F) ∈ levelSubgroup F n 0 ↔ _
      rw [levelSubgroup_zero]
    rw [hu]
    have hunit : ∀ a : Fˣ, a ∈ integralUnits v.integer ↔ v (a : F) = 1 :=
      fun a => ⟨valuation_eq_one_of_mem_integralUnits v, mem_integralUnits_of_valuation_eq_one v⟩
    simp only [hunit]
  have hK1 : MeasurableSet (integralSubgroup v.integer 0 :
      Set (Langlands.GeneralLinear (0 + 1) F)) := by
    rw [← levelSubgroup_zero]
    exact (levelOpenSubgroup F 0 0).isOpen.measurableSet
  have hU : MeasurableSet (integralUnits v.integer : Set Fˣ) :=
    (integralUnits_isOpen _ (Valuation.isOpen_integer (v := v))).measurableSet
  have hSm : MeasurableSet S := hK1.prod (MeasurableSet.univ_pi fun _ => hU)
  rw [hpre, iwasawaMeasure, Measure.prod_prod, unipotentHaar_integral, mul_one, parameterMeasure,
    withDensity_apply _ hSm]
  have hone : ∀ b ∈ S, ((weight F n b : ℝ≥0) : ℝ≥0∞) = 1 := by
    intro b hb
    have hb' : ∀ i, v (torusCoord n b i : F) = 1 := by
      rw [torusCoord_valuation_iff]
      exact ⟨hb.1, fun i => valuation_eq_one_of_mem_integralUnits v (hb.2 i (Set.mem_univ i))⟩
    rw [weight_apply, torusModulus_eq_one F _ hb', inv_one, Units.val_one, ENNReal.coe_one]
  rw [setLIntegral_congr_fun hSm hone, setLIntegral_const, one_mul, hS, Measure.prod_prod,
    Measure.pi_pi]
  have h1 : generalLinearHaar F 0
      (integralSubgroup v.integer 0 : Set (Langlands.GeneralLinear (0 + 1) F)) = 1 :=
    generalLinearHaar_integralSubgroup F 0
  rw [h1, one_mul]
  have hU1 : localMultiplicativeHaar F (integralUnits v.integer : Set Fˣ) = 1 :=
    localMultiplicativeHaar_integerUnits F
  simp only [hU1, Finset.prod_const_one]

/-- **Iwasawa integration with constant one.** Haar measure on `GL_(n+1)` is the
pushforward of the parameter measure times Haar measure restricted to `GL_(n+1)(O)`
under `(x, k) ↦ point x * k`. -/
theorem map_iwasawaMeasure_prod (n : ℕ) :
    Measure.map (fun x : ((Langlands.GeneralLinear (0 + 1) F × (Fin n → Fˣ)) ×
        upperUnipotent (n + 1) F) × Langlands.GeneralLinear (n + 1) F =>
        point x.1 * x.2)
      ((iwasawaMeasure F n).prod ((generalLinearHaar F n).restrict
        (integralSubgroup (ValuativeRel.valuation F).integer n :
          Set (Langlands.GeneralLinear (n + 1) F)))) =
      generalLinearHaar F n := by
  set v := ValuativeRel.valuation F
  have hK : MeasurableSet (integralSubgroup v.integer n :
      Set (Langlands.GeneralLinear (n + 1) F)) := by
    rw [← levelSubgroup_zero]
    exact (levelOpenSubgroup F n 0).isOpen.measurableSet
  have hmeas : Measurable (fun x : ((Langlands.GeneralLinear (0 + 1) F ×
      (Fin n → Fˣ)) × upperUnipotent (n + 1) F) ×
        Langlands.GeneralLinear (n + 1) F => point x.1 * x.2) :=
    ((measurable_point F n).comp measurable_fst).mul measurable_snd
  ext s hs
  rw [Measure.map_apply hmeas hs, Measure.prod_apply_symm (hmeas hs)]
  have key := CompactFactorization.lintegral_restrict_lintegral_mul
    (generalLinearHaar F n) (integralSubgroup v.integer n) hK (iwasawaMeasure F n)
    point (measurable_point F n) (exists_point_mul v)
    (fun x₀ => ⟨shift x₀, measurePreserving_shift F n x₀, point_shift x₀⟩)
    (s.indicator 1) (measurable_one.indicator hs)
  rw [iwasawaMeasure_point_preimage, one_mul, lintegral_indicator_one hs] at key
  rw [← key]
  apply lintegral_congr
  intro k
  rw [← lintegral_indicator_one (s := (fun x => (x, k)) ⁻¹'
    ((fun x : ((Langlands.GeneralLinear (0 + 1) F × (Fin n → Fˣ)) ×
      upperUnipotent (n + 1) F) × Langlands.GeneralLinear (n + 1) F =>
        point x.1 * x.2) ⁻¹' s)) ((hmeas hs).preimage (measurable_id.prodMk measurable_const))]
  apply lintegral_congr
  intro x
  rfl

/-- The measure `|det g|⁻ⁿ dg` on `GL₁`, the `GL₁` part of the density. -/
def glOneMeasure (n : ℕ) : Measure (Langlands.GeneralLinear (0 + 1) F) :=
  (generalLinearHaar F 0).withDensity fun g => (weight F n (g, 1) : ℝ≥0∞)

/-- The measure `ω(1, a) da` on the torus tail `(Fˣ)ⁿ`. -/
def tailMeasure (n : ℕ) : Measure (Fin n → Fˣ) :=
  (Measure.pi fun _ : Fin n => localMultiplicativeHaar F).withDensity
    fun a => (weight F n (1, a) : ℝ≥0∞)

instance glOneMeasure_sigmaFinite (n : ℕ) : SigmaFinite (glOneMeasure F n) := by
  unfold glOneMeasure
  infer_instance

instance tailMeasure_sigmaFinite (n : ℕ) : SigmaFinite (tailMeasure F n) := by
  unfold tailMeasure
  infer_instance

theorem parameterMeasure_eq_prod (n : ℕ) :
    parameterMeasure F n = (glOneMeasure F n).prod (tailMeasure F n) := by
  have hw := (continuous_weight F n).measurable
  have h0 : Measurable fun g : Langlands.GeneralLinear (0 + 1) F =>
      (weight F n (g, 1) : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp (hw.comp (measurable_id.prodMk measurable_const))
  have h1 : Measurable fun a : Fin n → Fˣ => (weight F n (1, a) : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp (hw.comp (measurable_const.prodMk measurable_id))
  rw [glOneMeasure, tailMeasure, prod_withDensity h0 h1, parameterMeasure]
  congr 1
  funext b
  rw [weight_split F b, ENNReal.coe_mul]

/-- The rearranged measure on `(GL₁ × ((Fˣ)ⁿ × GL_(n+1))) × N`: the unipotent variable
is innermost and the `GL₁` variable outermost. -/
def unfoldedMeasure (n : ℕ) :
    Measure ((Langlands.GeneralLinear (0 + 1) F × ((Fin n → Fˣ) ×
      Langlands.GeneralLinear (n + 1) F)) × upperUnipotent (n + 1) F) :=
  ((glOneMeasure F n).prod ((tailMeasure F n).prod ((generalLinearHaar F n).restrict
    (integralSubgroup (ValuativeRel.valuation F).integer n :
      Set (Langlands.GeneralLinear (n + 1) F))))).prod (unipotentHaar F n)

/-- The point `u · diag(det g / ∏ a, a) · k` of the rearranged parameters. -/
def unfoldedPoint {n : ℕ}
    (x : (Langlands.GeneralLinear (0 + 1) F × ((Fin n → Fˣ) ×
      Langlands.GeneralLinear (n + 1) F)) × upperUnipotent (n + 1) F) :
    Langlands.GeneralLinear (n + 1) F :=
  point ((x.1.1, x.1.2.1), x.2) * x.1.2.2

theorem measurable_unfoldedPoint (n : ℕ) : Measurable (unfoldedPoint F (n := n)) :=
  ((measurable_point F n).comp ((measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk
    measurable_snd)).mul measurable_fst.snd.snd

/-- **Unfolded Iwasawa integration.** Haar measure on `GL_(n+1)` is the pushforward of
`(|det g|⁻ⁿ dg × ω(1, a) da × dk|_K) × du` under `((g, (a, k)), u) ↦ u D(g, a) k`. -/
theorem map_unfoldedMeasure (n : ℕ) :
    Measure.map (unfoldedPoint F (n := n)) (unfoldedMeasure F n) =
      generalLinearHaar F n := by
  set dk := (generalLinearHaar F n).restrict
    (integralSubgroup (ValuativeRel.valuation F).integer n :
      Set (Langlands.GeneralLinear (n + 1) F))
  set e : (Langlands.GeneralLinear (0 + 1) F × ((Fin n → Fˣ) ×
      Langlands.GeneralLinear (n + 1) F)) × upperUnipotent (n + 1) F →
      ((Langlands.GeneralLinear (0 + 1) F × (Fin n → Fˣ)) ×
        upperUnipotent (n + 1) F) × Langlands.GeneralLinear (n + 1) F :=
    fun x => (((x.1.1, x.1.2.1), x.2), x.1.2.2) with he_def
  have he : MeasurePreserving e (unfoldedMeasure F n) ((iwasawaMeasure F n).prod dk) := by
    rw [iwasawaMeasure, parameterMeasure_eq_prod]
    have h1 := (measurePreserving_prodAssoc (glOneMeasure F n) (tailMeasure F n) dk).symm
    have h2 := h1.prod (MeasurePreserving.id (unipotentHaar F n))
    have h3 := measurePreserving_prodAssoc ((glOneMeasure F n).prod (tailMeasure F n)) dk
      (unipotentHaar F n)
    have h4 := (MeasurePreserving.id ((glOneMeasure F n).prod (tailMeasure F n))).prod
      (Measure.measurePreserving_swap (μ := dk) (ν := unipotentHaar F n))
    have h5 := (measurePreserving_prodAssoc ((glOneMeasure F n).prod (tailMeasure F n))
      (unipotentHaar F n) dk).symm
    convert h5.comp (h4.comp (h3.comp h2)) using 1
    · funext x
      rfl
    · rfl
  have hπ : Measurable (fun x : ((Langlands.GeneralLinear (0 + 1) F ×
      (Fin n → Fˣ)) × upperUnipotent (n + 1) F) ×
        Langlands.GeneralLinear (n + 1) F => point x.1 * x.2) :=
    ((measurable_point F n).comp measurable_fst).mul measurable_snd
  rw [show unfoldedPoint F (n := n) = (fun x : ((Langlands.GeneralLinear (0 + 1) F ×
      (Fin n → Fˣ)) × upperUnipotent (n + 1) F) ×
        Langlands.GeneralLinear (n + 1) F => point x.1 * x.2) ∘ e from rfl,
    ← Measure.map_map hπ he.measurable, he.map_eq, map_iwasawaMeasure_prod]

end Measure

end Langlands.AllField.RankinSelberg.RankOneIwasawa
