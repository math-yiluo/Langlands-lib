import Langlands.Representation.RankinSelberg.DiagonalUnipotentHaar
import Langlands.Analysis.Local.CompactFactorizationIntegral
import Langlands.Group.GL.SingletonBlocks
import Langlands.Group.GL.BlockModulusHaarProof
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity
import Langlands.Representation.RankinSelberg.IwasawaTorusPartitionProof
import Langlands.Representation.Whittaker.Iwasawa
import Mathlib.Topology.Algebra.IsOpenUnits

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

namespace Langlands.RankinSelberg.RankOneIwasawa

open GeneralLinear GeneralLinear.BlockShape

universe uF

section Algebra

variable {E : Type*} [Field E]

/-- The torus coordinate `(g, a) ↦ (det g / ∏ a, a)`, a group homomorphism. -/
def torusCoord (n : ℕ) :
    Langlands.GeneralLinear (0 + 1) E × (Fin n → Eˣ) →* (Fin (n + 1) → Eˣ) where
  toFun b := Fin.cons (Matrix.GeneralLinearGroup.det b.1 * (∏ i, b.2 i)⁻¹) b.2
  map_one' := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ i => simp
  map_mul' b c := by
    funext i
    induction i using Fin.cases with
    | zero =>
      simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Pi.mul_apply, Finset.prod_mul_distrib,
        mul_inv, Fin.cons_zero]
      exact mul_mul_mul_comm _ _ _ _
    | succ i => simp

@[simp] theorem torusCoord_zero {n : ℕ} (b : Langlands.GeneralLinear (0 + 1) E × (Fin n → Eˣ)) :
    torusCoord n b 0 = Matrix.GeneralLinearGroup.det b.1 * (∏ i, b.2 i)⁻¹ := rfl

@[simp] theorem torusCoord_succ {n : ℕ} (b : Langlands.GeneralLinear (0 + 1) E × (Fin n → Eˣ))
    (i : Fin n) : torusCoord n b i.succ = b.2 i := rfl

/-- A section of the torus coordinate. -/
def torusSection {n : ℕ} (t : Fin (n + 1) → Eˣ) :
    Langlands.GeneralLinear (0 + 1) E × (Fin n → Eˣ) :=
  (Iwasawa.diagonalUnits fun _ => t 0 * ∏ i : Fin n, t i.succ, Fin.tail t)

theorem det_diagonalUnits {m : ℕ} (d : Fin m → Eˣ) :
    Matrix.GeneralLinearGroup.det (Iwasawa.diagonalUnits d) = ∏ i, d i := by
  ext
  simp [Matrix.det_diagonal]

@[simp] theorem torusCoord_torusSection {n : ℕ} (t : Fin (n + 1) → Eˣ) :
    torusCoord n (torusSection t) = t := by
  funext i
  induction i using Fin.cases with
  | zero =>
    simp only [torusSection, torusCoord_zero, det_diagonalUnits, Fin.prod_univ_succ,
      Fin.prod_univ_zero, mul_one, Fin.tail]
    rw [mul_inv_cancel_right]
  | succ i => exact torusCoord_succ _ i

/-- The parametrization point `u * diag(det g / ∏ a, a)`. -/
def point {n : ℕ} (x : (Langlands.GeneralLinear (0 + 1) E × (Fin n → Eˣ)) ×
    upperUnipotent (n + 1) E) : Langlands.GeneralLinear (n + 1) E :=
  (x.2 : Langlands.GeneralLinear (n + 1) E) * Iwasawa.diagonalUnits (torusCoord n x.1)

theorem continuous_diagonalUnits' [TopologicalSpace E] {m : ℕ} :
    Continuous (Iwasawa.diagonalUnits (m := m) (F := E)) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact (continuous_pi fun i => Units.continuous_val.comp (continuous_apply i)).matrix_diagonal
  · exact (continuous_pi fun i =>
      Units.continuous_coe_inv.comp (continuous_apply i)).matrix_diagonal

/-- Left translation in the parameters: `point (shift x₀ x) = (point x₀)⁻¹ * point x`. -/
def shift {n : ℕ}
    (x₀ x : (Langlands.GeneralLinear (0 + 1) E × (Fin n → Eˣ)) × upperUnipotent (n + 1) E) :
    (Langlands.GeneralLinear (0 + 1) E × (Fin n → Eˣ)) × upperUnipotent (n + 1) E :=
  (x₀.1⁻¹ * x.1, diagonalConj (torusCoord n x₀.1)⁻¹ (x₀.2⁻¹ * x.2))

theorem point_shift {n : ℕ}
    (x₀ x : (Langlands.GeneralLinear (0 + 1) E × (Fin n → Eˣ)) × upperUnipotent (n + 1) E) :
    point (shift x₀ x) = (point x₀)⁻¹ * point x := by
  simp only [point, shift, diagonalConj_val, map_mul, map_inv, Subgroup.coe_mul,
    Subgroup.coe_inv]
  group

end Algebra

section Valued

variable {E : Type*} [Field E] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation E Γ₀)

open Conductor

/-- The determinant of a `1 × 1` invertible matrix is its entry. -/
theorem det_glOne (b : Langlands.GeneralLinear (0 + 1) E) :
    ((Matrix.GeneralLinearGroup.det b : Eˣ) : E) = b 0 0 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_fin_one _

/-- A `1 × 1` invertible matrix is integral exactly when its determinant has valuation one. -/
theorem mem_integralSubgroup_zero_iff (b : Langlands.GeneralLinear (0 + 1) E) :
    b ∈ integralSubgroup v.integer 0 ↔ v ((Matrix.GeneralLinearGroup.det b : Eˣ) : E) = 1 := by
  rw [det_glOne]
  constructor
  · intro hb
    exact Iwasawa.valuation_diag_eq_one v hb (fun i j h => absurd h (by omega)) 0
  · intro hb
    have he : b = Iwasawa.diagonalUnits (fun _ => Matrix.GeneralLinearGroup.det b) := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      obtain rfl : i = 0 := Fin.ext (by have := i.isLt; omega)
      obtain rfl : j = 0 := Fin.ext (by have := j.isLt; omega)
      simp
    rw [he]
    apply Iwasawa.diagonalUnits_mem
    intro i
    rw [det_glOne, hb]

/-- The torus coordinate is integral exactly on integral parameters. -/
theorem torusCoord_valuation_iff {n : ℕ}
    (b : Langlands.GeneralLinear (0 + 1) E × (Fin n → Eˣ)) :
    (∀ i, v (torusCoord n b i : E) = 1) ↔
      b.1 ∈ integralSubgroup v.integer 0 ∧ ∀ i, v (b.2 i : E) = 1 := by
  rw [mem_integralSubgroup_zero_iff]
  have hprod : v ((∏ i, b.2 i : Eˣ) : E) = ∏ i, v (b.2 i : E) := by
    rw [Units.coe_prod, map_prod]
  constructor
  · intro h
    have h2 : ∀ i, v (b.2 i : E) = 1 := fun i => by simpa using h i.succ
    refine ⟨?_, h2⟩
    have h0 := h 0
    rw [torusCoord_zero, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hprod,
      Finset.prod_eq_one (fun i _ => h2 i), inv_one, mul_one] at h0
    exact h0
  · rintro ⟨h1, h2⟩ i
    induction i using Fin.cases with
    | zero =>
      rw [torusCoord_zero, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hprod,
        Finset.prod_eq_one (fun i _ => h2 i), inv_one, mul_one, h1]
    | succ i => simpa using h2 i

/-- The parametrization point is integral exactly when its torus coordinate is a unit
vector and its unipotent coordinate is integral. -/
theorem point_mem_integralSubgroup_iff {n : ℕ}
    (x : (Langlands.GeneralLinear (0 + 1) E × (Fin n → Eˣ)) × upperUnipotent (n + 1) E) :
    point x ∈ integralSubgroup v.integer n ↔
      (∀ i, v (torusCoord n x.1 i : E) = 1) ∧
        (x.2 : Langlands.GeneralLinear (n + 1) E) ∈ integralSubgroup v.integer n := by
  constructor
  · intro hx
    have hup : (point x).val.IsUpperTriangular := by
      change ((x.2 : Langlands.GeneralLinear (n + 1) E).val *
        (Iwasawa.diagonalUnits (torusCoord n x.1)).val).IsUpperTriangular
      rw [Iwasawa.diagonalUnits_val]
      exact x.2.property.1.mul (Matrix.blockTriangular_diagonal _)
    have hdiag : ∀ i, v (torusCoord n x.1 i : E) = 1 := by
      intro i
      have h := Iwasawa.valuation_diag_eq_one v hx hup i
      have he : (point x) i i = (torusCoord n x.1 i : E) := by
        change ((x.2 : Langlands.GeneralLinear (n + 1) E).val *
          (Iwasawa.diagonalUnits (torusCoord n x.1)).val) i i = _
        rw [Iwasawa.diagonalUnits_val, Matrix.mul_diagonal, UpperUnipotent.entry_diag, one_mul]
      rwa [he] at h
    refine ⟨hdiag, ?_⟩
    have hD := Iwasawa.diagonalUnits_mem v (torusCoord n x.1) hdiag
    have : (x.2 : Langlands.GeneralLinear (n + 1) E) =
        point x * (Iwasawa.diagonalUnits (torusCoord n x.1))⁻¹ := by
      rw [point, mul_inv_cancel_right]
    rw [this]
    exact mul_mem hx (inv_mem hD)
  · rintro ⟨hdiag, hu⟩
    exact mul_mem hu (Iwasawa.diagonalUnits_mem v (torusCoord n x.1) hdiag)

/-- Every invertible matrix is a parametrization point times an integral matrix. -/
theorem exists_point_mul {n : ℕ} (y : Langlands.GeneralLinear (n + 1) E) :
    ∃ x : (Langlands.GeneralLinear (0 + 1) E × (Fin n → Eˣ)) × upperUnipotent (n + 1) E,
      ∃ k ∈ integralSubgroup v.integer n, y = point x * k := by
  obtain ⟨b, hb, k, hk, rfl⟩ := Iwasawa.exists_upperTriangular_mul v y
  have hd : ∀ i, b i i ≠ 0 := by
    intro i h0
    apply Matrix.GeneralLinearGroup.det_ne_zero b
    rw [Matrix.det_of_isUpperTriangular hb]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  set d : Fin (n + 1) → Eˣ := fun i => Units.mk0 (b i i) (hd i) with hdd
  have hval : (b * (Iwasawa.diagonalUnits d)⁻¹).val = b.val * Matrix.diagonal fun i => (b i i)⁻¹ := by
    rw [Units.val_mul, ← map_inv, Iwasawa.diagonalUnits_val]
    congr 1
  have hu : b * (Iwasawa.diagonalUnits d)⁻¹ ∈ upperUnipotent (n + 1) E := by
    refine ⟨?_, fun i => ?_⟩
    · rw [hval]
      exact hb.mul (Matrix.blockTriangular_diagonal _)
    · change (b * (Iwasawa.diagonalUnits d)⁻¹).val i i = 1
      rw [hval, Matrix.mul_diagonal, mul_inv_cancel₀ (hd i)]
  refine ⟨(torusSection d, ⟨_, hu⟩), k, hk, ?_⟩
  simp only [point, torusCoord_torusSection, inv_mul_cancel_right]

end Valued

section Measure

open Conductor

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance (m : ℕ) : MeasurableSpace (Langlands.GeneralLinear (m + 1) F.Carrier) := borel _
local instance (m : ℕ) : BorelSpace (Langlands.GeneralLinear (m + 1) F.Carrier) := ⟨rfl⟩
local instance (m : ℕ) : MeasurableSpace (upperUnipotent (m + 1) F.Carrier) := borel _
local instance (m : ℕ) : BorelSpace (upperUnipotent (m + 1) F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace F.Carrierˣ := borel _
local instance : BorelSpace F.Carrierˣ := ⟨rfl⟩

local instance matrixLocallyCompact (m : ℕ) :
    LocallyCompactSpace (Matrix (Fin m) (Fin m) F.Carrier) :=
  inferInstanceAs (LocallyCompactSpace (Fin m → Fin m → F.Carrier))

local instance glLocallyCompact (m : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear m F.Carrier) :=
  inferInstance

local instance glSecondCountable (m : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear m F.Carrier) := by
  have : SecondCountableTopology (Matrix (Fin m) (Fin m) F.Carrier) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin m → F.Carrier))
  have : SecondCountableTopology (Matrix (Fin m) (Fin m) F.Carrier)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

local instance unipotentSecondCountable (m : ℕ) :
    SecondCountableTopology (upperUnipotent m F.Carrier) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (upperUnipotent m F.Carrier : Set (Langlands.GeneralLinear m F.Carrier))

local instance unipotentLocallyCompact (m : ℕ) :
    LocallyCompactSpace (upperUnipotent m F.Carrier) :=
  UpperUnipotent.locallyCompactSpace

local instance unitsSecondCountable : SecondCountableTopology F.Carrierˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

local instance unitsLocallyCompact : LocallyCompactSpace F.Carrierˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := F.Carrier)).locallyCompactSpace

/-- The root modulus `δ(t) = ∏_{i<j} |t_i / t_j|` of the diagonal torus. -/
def torusModulus (m : ℕ) : (Fin m → F.Carrierˣ) →* ℝ≥0ˣ :=
  (F.canonicalTopologicalData.leviModulus (singletons m)).comp (singletonLevi F.Carrier)

theorem torusModulus_apply {m : ℕ} (t : Fin m → F.Carrierˣ) :
    torusModulus F m t = ∏ i : Fin m, ∏ j ∈ Finset.univ.filter (fun j => i < j),
      F.canonicalTopologicalData.normalizedAbsUnits (t i) /
        F.canonicalTopologicalData.normalizedAbsUnits (t j) :=
  F.canonicalTopologicalData.leviModulus_singletonLevi t

theorem continuous_torusModulus (m : ℕ) : Continuous (torusModulus F m) := by
  have hc := F.canonicalTopologicalData.continuous_normalizedAbsUnits
  simp_rw [funext (torusModulus_apply F (m := m))]
  refine continuous_finsetProd _ fun i _ => continuous_finsetProd _ fun j _ => ?_
  exact (hc.comp (continuous_apply i)).div' (hc.comp (continuous_apply j))

/-- The modulus is one on integral units. -/
theorem torusModulus_eq_one {m : ℕ} (t : Fin m → F.Carrierˣ)
    (ht : ∀ i, ValuativeRel.valuation F.Carrier (t i : F.Carrier) = 1) :
    torusModulus F m t = 1 := by
  have h1 : ∀ i, F.canonicalTopologicalData.normalizedAbsUnits (t i) = 1 := by
    intro i
    apply Units.ext
    apply NNReal.eq
    rw [F.canonicalTopologicalData.normalizedAbsUnits_coe, Units.val_one, NNReal.coe_one,
      F.canonicalTopologicalData.normalizedAbs_eq_one_iff_discreteValuation]
    change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
      (ValuativeRel.valuation F.Carrier (t i : F.Carrier)) = 1
    rw [ht i, map_one]
  rw [torusModulus_apply]
  simp [h1]

theorem continuous_det_units (m : ℕ) :
    Continuous (fun g : Langlands.GeneralLinear m F.Carrier =>
      Matrix.GeneralLinearGroup.det g) := by
  apply Units.continuous_iff.2
  constructor
  · have : (Units.val ∘ fun g : Langlands.GeneralLinear m F.Carrier =>
        Matrix.GeneralLinearGroup.det g) =
        fun g : Langlands.GeneralLinear m F.Carrier =>
          (g : Matrix (Fin m) (Fin m) F.Carrier).det :=
      funext fun g => Matrix.GeneralLinearGroup.val_det_apply g
    rw [this]
    exact Units.continuous_val.matrix_det
  · have : (fun g : Langlands.GeneralLinear m F.Carrier =>
        (((Matrix.GeneralLinearGroup.det g)⁻¹ : F.Carrierˣ) : F.Carrier)) =
        fun g => ((g⁻¹ : Langlands.GeneralLinear m F.Carrier) :
          Matrix (Fin m) (Fin m) F.Carrier).det := by
      funext g
      rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact Units.continuous_coe_inv.matrix_det

theorem continuous_torusCoord (n : ℕ) :
    Continuous (torusCoord (E := F.Carrier) n) := by
  refine continuous_pi fun i => ?_
  induction i using Fin.cases with
  | zero =>
    change Continuous fun b : Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ) =>
      Matrix.GeneralLinearGroup.det b.1 * (∏ i, b.2 i)⁻¹
    exact ((continuous_det_units F _).comp continuous_fst).mul
      (continuous_finsetProd _ fun i _ => (continuous_apply i).comp continuous_snd).inv
  | succ i =>
    change Continuous fun b : Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ) =>
      b.2 i
    exact (continuous_apply i).comp continuous_snd

/-- The density `ω(b) = δ(D(b))⁻¹` on the parameter group `GL_1 × (Fˣ)ⁿ`. -/
def weight (n : ℕ) :
    Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ) →* ℝ≥0 :=
  (Units.coeHom ℝ≥0).comp ((torusModulus F (n + 1)).comp (torusCoord n))⁻¹

theorem weight_apply {n : ℕ} (b : Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) :
    weight F n b = ((torusModulus F (n + 1) (torusCoord n b))⁻¹ : ℝ≥0ˣ) := rfl

theorem continuous_weight (n : ℕ) : Continuous (weight F n) := by
  change Continuous fun b => (((torusModulus F (n + 1) (torusCoord n b))⁻¹ : ℝ≥0ˣ) : ℝ≥0)
  exact Units.continuous_val.comp
    (((continuous_torusModulus F (n + 1)).comp (continuous_torusCoord F n)).inv)



/-- The parameter measure: Haar measure on `GL_1 × (Fˣ)ⁿ` with density `ω`. -/
def parameterMeasure (n : ℕ) :
    Measure (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) :=
  ((generalLinearHaar F.Carrier 0).prod
      (Measure.pi fun _ : Fin n => localMultiplicativeHaar F.Carrier)).withDensity
    fun b => (weight F n b : ℝ≥0∞)

/-- The measure on the full parameter space `(GL_1 × (Fˣ)ⁿ) × N`. -/
def iwasawaMeasure (n : ℕ) :
    Measure ((Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
      upperUnipotent (n + 1) F.Carrier) :=
  (parameterMeasure F n).prod (unipotentHaar F.Carrier n)

instance parameterMeasure_sigmaFinite (n : ℕ) : SigmaFinite (parameterMeasure F n) := by
  unfold parameterMeasure
  infer_instance

instance iwasawaMeasure_sFinite (n : ℕ) : SFinite (iwasawaMeasure F n) := by
  unfold iwasawaMeasure
  infer_instance

local instance parameterBase_isMulLeftInvariant (n : ℕ) :
    ((generalLinearHaar F.Carrier 0).prod
      (Measure.pi fun _ : Fin n => localMultiplicativeHaar F.Carrier)).IsMulLeftInvariant :=
  Measure.prod.instIsMulLeftInvariant

/-- The modulus of `diag(x, 1, …, 1)` is `|x|ⁿ`. -/
theorem torusModulus_cons_one {n : ℕ} (x : F.Carrierˣ) :
    torusModulus F (n + 1) (Fin.cons x 1) =
      F.canonicalTopologicalData.normalizedAbsUnits x ^ n := by
  rw [torusModulus_apply]
  simp_rw [Finset.prod_filter]
  rw [Fin.prod_univ_succ]
  have h0 : (∏ j : Fin (n + 1), if (0 : Fin (n + 1)) < j then
      F.canonicalTopologicalData.normalizedAbsUnits ((Fin.cons x 1 : Fin (n + 1) → F.Carrierˣ) 0) /
        F.canonicalTopologicalData.normalizedAbsUnits ((Fin.cons x 1 : Fin (n + 1) → F.Carrierˣ) j)
      else 1) = F.canonicalTopologicalData.normalizedAbsUnits x ^ n := by
    rw [Fin.prod_univ_succ]
    simp [Fin.succ_pos]
  have h1 : ∀ i : Fin n, (∏ j : Fin (n + 1), if i.succ < j then
      F.canonicalTopologicalData.normalizedAbsUnits
        ((Fin.cons x 1 : Fin (n + 1) → F.Carrierˣ) i.succ) /
        F.canonicalTopologicalData.normalizedAbsUnits ((Fin.cons x 1 : Fin (n + 1) → F.Carrierˣ) j)
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
theorem weight_glOne {n : ℕ} (g : Langlands.GeneralLinear (0 + 1) F.Carrier) :
    weight F n (g, 1) =
      ((F.canonicalTopologicalData.normalizedAbsUnits (Matrix.GeneralLinearGroup.det g) :
        ℝ≥0) ^ n)⁻¹ := by
  have ht : torusCoord n (g, (1 : Fin n → F.Carrierˣ)) =
      Fin.cons (Matrix.GeneralLinearGroup.det g) 1 := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ i => simp
  rw [weight_apply, ht, torusModulus_cons_one, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]

/-- The density splits over the `GL₁` and torus factors. -/
theorem weight_split {n : ℕ} (b : Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) :
    weight F n b = weight F n (b.1, 1) * weight F n (1, b.2) := by
  rw [← map_mul]
  congr 1
  ext <;> simp

/-- The determinant of a parametrization point is the determinant of its `GL₁`
coordinate. -/
theorem det_point {n : ℕ}
    (x : (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
      upperUnipotent (n + 1) F.Carrier) :
    Matrix.GeneralLinearGroup.det (point x) = Matrix.GeneralLinearGroup.det x.1.1 := by
  rw [point, map_mul, det_diagonalUnits, Fin.prod_univ_succ, torusCoord_zero]
  have hu : Matrix.GeneralLinearGroup.det (x.2 : Langlands.GeneralLinear (n + 1) F.Carrier) = 1 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
      Matrix.det_of_isUpperTriangular x.2.property.1]
    exact Finset.prod_eq_one fun i _ => UpperUnipotent.entry_diag x.2 i
  simp only [torusCoord_succ, hu, one_mul, inv_mul_cancel_right]

/-- Diagonal conjugation scales the normalized unipotent Haar measure by `δ⁻¹`. -/
theorem unipotentConj_map (n : ℕ) (a : Fin (n + 1) → F.Carrierˣ) :
    (unipotentHaar F.Carrier n).map (diagonalConj a) =
      ((torusModulus F (n + 1) a : ℝ≥0)⁻¹) • unipotentHaar F.Carrier n := by
  exact diagonalConj_map F F.canonicalTopologicalData n a

/-- Left translation of a measure with a multiplicative density. -/
theorem map_mul_left_withDensity {B : Type*} [Group B] [MeasurableSpace B] [MeasurableMul B]
    (ν : Measure B) [ν.IsMulLeftInvariant] (ω : B →* ℝ≥0) (hω : Measurable ω) (h : B) :
    (ν.withDensity fun b => (ω b : ℝ≥0∞)).map (h * ·) =
      ((ω h⁻¹ : ℝ≥0) : ℝ≥0∞) • ν.withDensity fun b => (ω b : ℝ≥0∞) := by
  have hωm : Measurable fun b => (ω b : ℝ≥0∞) := measurable_coe_nnreal_ennreal.comp hω
  ext s hs
  have hs' : MeasurableSet ((h * ·) ⁻¹' s) := measurable_const_mul h hs
  rw [Measure.map_apply (measurable_const_mul h) hs, Measure.smul_apply, withDensity_apply _ hs,
    withDensity_apply _ hs', smul_eq_mul, ← lintegral_indicator hs', ← lintegral_indicator hs,
    ← lintegral_const_mul _ (hωm.indicator hs)]
  have := lintegral_mul_left_eq_self (μ := ν)
    (((h * ·) ⁻¹' s).indicator fun b => (ω b : ℝ≥0∞)) h⁻¹
  rw [← this]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem (show h⁻¹ * x ∈ (h * ·) ⁻¹' s by simpa using hx),
      Set.indicator_of_mem hx, map_mul, ENNReal.coe_mul]
  · rw [Set.indicator_of_notMem (show h⁻¹ * x ∉ (h * ·) ⁻¹' s by simpa using hx),
      Set.indicator_of_notMem hx, mul_zero]

theorem continuous_point (n : ℕ) :
    Continuous (point (E := F.Carrier) (n := n)) :=
  (continuous_subtype_val.comp continuous_snd).mul
    (continuous_diagonalUnits'.comp ((continuous_torusCoord F n).comp continuous_fst))

theorem measurable_point (n : ℕ) : Measurable (point (E := F.Carrier) (n := n)) :=
  (continuous_point F n).measurable

/-- Left translation in parameters preserves the parameter measure. -/
theorem measurePreserving_shift (n : ℕ)
    (x₀ : (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
      upperUnipotent (n + 1) F.Carrier) :
    MeasurePreserving (shift x₀) (iwasawaMeasure F n) (iwasawaMeasure F n) := by
  have hf : Measurable fun b : Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ) =>
      x₀.1⁻¹ * b := (continuous_const.mul continuous_id).measurable
  have hg : Measurable fun u : upperUnipotent (n + 1) F.Carrier =>
      diagonalConj (torusCoord n x₀.1)⁻¹ (x₀.2⁻¹ * u) :=
    ((continuous_diagonalConj _).comp (continuous_const.mul continuous_id)).measurable
  refine ⟨hf.prodMap hg, ?_⟩
  change Measure.map (Prod.map (fun b => x₀.1⁻¹ * b)
    (fun u => diagonalConj (torusCoord n x₀.1)⁻¹ (x₀.2⁻¹ * u)))
      ((parameterMeasure F n).prod (unipotentHaar F.Carrier n)) = _
  rw [← Measure.map_prod_map _ _ hf hg]
  have h1 : (parameterMeasure F n).map (fun b => x₀.1⁻¹ * b) =
      ((weight F n x₀.1 : ℝ≥0) : ℝ≥0∞) • parameterMeasure F n := by
    have := map_mul_left_withDensity ((generalLinearHaar F.Carrier 0).prod
      (Measure.pi fun _ : Fin n => localMultiplicativeHaar F.Carrier)) (weight F n)
      (continuous_weight F n).measurable x₀.1⁻¹
    rw [inv_inv] at this
    exact this
  have h2 : (unipotentHaar F.Carrier n).map
      (fun u => diagonalConj (torusCoord n x₀.1)⁻¹ (x₀.2⁻¹ * u)) =
      ((torusModulus F (n + 1) (torusCoord n x₀.1)⁻¹ : ℝ≥0)⁻¹) • unipotentHaar F.Carrier n := by
    have hm : Measurable fun u : upperUnipotent (n + 1) F.Carrier => x₀.2⁻¹ * u :=
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
      (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
        Set (Langlands.GeneralLinear (n + 1) F.Carrier))) = 1 := by
  set v := ValuativeRel.valuation F.Carrier
  set S : Set (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) :=
    (integralSubgroup v.integer 0 : Set (Langlands.GeneralLinear (0 + 1) F.Carrier)) ×ˢ
      Set.univ.pi fun _ => (integralUnits v.integer : Set F.Carrierˣ) with hS
  have hpre : point ⁻¹' (integralSubgroup v.integer n :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier)) =
      S ×ˢ (unipotentIntegralOpen F.Carrier n : Set (upperUnipotent (n + 1) F.Carrier)) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, Set.mem_prod, Set.mem_univ_pi, hS]
    rw [point_mem_integralSubgroup_iff, torusCoord_valuation_iff]
    have hu : x.2 ∈ unipotentIntegralOpen F.Carrier n ↔
        (x.2 : Langlands.GeneralLinear (n + 1) F.Carrier) ∈ integralSubgroup v.integer n := by
      change (x.2 : Langlands.GeneralLinear (n + 1) F.Carrier) ∈ levelSubgroup F.Carrier n 0 ↔ _
      rw [levelSubgroup_zero]
    rw [hu]
    have hunit : ∀ a : F.Carrierˣ, a ∈ integralUnits v.integer ↔ v (a : F.Carrier) = 1 :=
      fun a => ⟨valuation_eq_one_of_mem_integralUnits v, mem_integralUnits_of_valuation_eq_one v⟩
    simp only [hunit]
  have hK1 : MeasurableSet (integralSubgroup v.integer 0 :
      Set (Langlands.GeneralLinear (0 + 1) F.Carrier)) := by
    rw [← levelSubgroup_zero]
    exact (levelOpenSubgroup F.Carrier 0 0).isOpen.measurableSet
  have hU : MeasurableSet (integralUnits v.integer : Set F.Carrierˣ) :=
    (integralUnits_isOpen _ (Valuation.isOpen_integer (v := v))).measurableSet
  have hSm : MeasurableSet S := hK1.prod (MeasurableSet.univ_pi fun _ => hU)
  rw [hpre, iwasawaMeasure, Measure.prod_prod, unipotentHaar_integral, mul_one, parameterMeasure,
    withDensity_apply _ hSm]
  have hone : ∀ b ∈ S, ((weight F n b : ℝ≥0) : ℝ≥0∞) = 1 := by
    intro b hb
    have hb' : ∀ i, v (torusCoord n b i : F.Carrier) = 1 := by
      rw [torusCoord_valuation_iff]
      exact ⟨hb.1, fun i => valuation_eq_one_of_mem_integralUnits v (hb.2 i (Set.mem_univ i))⟩
    rw [weight_apply, torusModulus_eq_one F _ hb', inv_one, Units.val_one, ENNReal.coe_one]
  rw [setLIntegral_congr_fun hSm hone, setLIntegral_const, one_mul, hS, Measure.prod_prod,
    Measure.pi_pi]
  have h1 : generalLinearHaar F.Carrier 0
      (integralSubgroup v.integer 0 : Set (Langlands.GeneralLinear (0 + 1) F.Carrier)) = 1 :=
    generalLinearHaar_integralSubgroup F.Carrier 0
  rw [h1, one_mul]
  have hU1 : localMultiplicativeHaar F.Carrier (integralUnits v.integer : Set F.Carrierˣ) = 1 :=
    localMultiplicativeHaar_integerUnits F.Carrier
  simp only [hU1, Finset.prod_const_one]

/-- **Iwasawa integration with constant one.** Haar measure on `GL_(n+1)` is the
pushforward of the parameter measure times Haar measure restricted to `GL_(n+1)(O)`
under `(x, k) ↦ point x * k`. -/
theorem map_iwasawaMeasure_prod (n : ℕ) :
    Measure.map (fun x : ((Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
        upperUnipotent (n + 1) F.Carrier) × Langlands.GeneralLinear (n + 1) F.Carrier =>
        point x.1 * x.2)
      ((iwasawaMeasure F n).prod ((generalLinearHaar F.Carrier n).restrict
        (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
          Set (Langlands.GeneralLinear (n + 1) F.Carrier)))) =
      generalLinearHaar F.Carrier n := by
  set v := ValuativeRel.valuation F.Carrier
  have hK : MeasurableSet (integralSubgroup v.integer n :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier)) := by
    rw [← levelSubgroup_zero]
    exact (levelOpenSubgroup F.Carrier n 0).isOpen.measurableSet
  have hmeas : Measurable (fun x : ((Langlands.GeneralLinear (0 + 1) F.Carrier ×
      (Fin n → F.Carrierˣ)) × upperUnipotent (n + 1) F.Carrier) ×
        Langlands.GeneralLinear (n + 1) F.Carrier => point x.1 * x.2) :=
    ((measurable_point F n).comp measurable_fst).mul measurable_snd
  ext s hs
  rw [Measure.map_apply hmeas hs, Measure.prod_apply_symm (hmeas hs)]
  have key := CompactFactorization.lintegral_restrict_lintegral_mul
    (generalLinearHaar F.Carrier n) (integralSubgroup v.integer n) hK (iwasawaMeasure F n)
    point (measurable_point F n) (exists_point_mul v)
    (fun x₀ => ⟨shift x₀, measurePreserving_shift F n x₀, point_shift x₀⟩)
    (s.indicator 1) (measurable_one.indicator hs)
  rw [iwasawaMeasure_point_preimage, one_mul, lintegral_indicator_one hs] at key
  rw [← key]
  apply lintegral_congr
  intro k
  rw [← lintegral_indicator_one (s := (fun x => (x, k)) ⁻¹'
    ((fun x : ((Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
      upperUnipotent (n + 1) F.Carrier) × Langlands.GeneralLinear (n + 1) F.Carrier =>
        point x.1 * x.2) ⁻¹' s)) ((hmeas hs).preimage (measurable_id.prodMk measurable_const))]
  apply lintegral_congr
  intro x
  rfl

/-- The measure `|det g|⁻ⁿ dg` on `GL₁`, the `GL₁` part of the density. -/
def glOneMeasure (n : ℕ) : Measure (Langlands.GeneralLinear (0 + 1) F.Carrier) :=
  (generalLinearHaar F.Carrier 0).withDensity fun g => (weight F n (g, 1) : ℝ≥0∞)

/-- The measure `ω(1, a) da` on the torus tail `(Fˣ)ⁿ`. -/
def tailMeasure (n : ℕ) : Measure (Fin n → F.Carrierˣ) :=
  (Measure.pi fun _ : Fin n => localMultiplicativeHaar F.Carrier).withDensity
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
  have h0 : Measurable fun g : Langlands.GeneralLinear (0 + 1) F.Carrier =>
      (weight F n (g, 1) : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp (hw.comp (measurable_id.prodMk measurable_const))
  have h1 : Measurable fun a : Fin n → F.Carrierˣ => (weight F n (1, a) : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp (hw.comp (measurable_const.prodMk measurable_id))
  rw [glOneMeasure, tailMeasure, prod_withDensity h0 h1, parameterMeasure]
  congr 1
  funext b
  rw [weight_split F b, ENNReal.coe_mul]

/-- The rearranged measure on `(GL₁ × ((Fˣ)ⁿ × GL_(n+1))) × N`: the unipotent variable
is innermost and the `GL₁` variable outermost. -/
def unfoldedMeasure (n : ℕ) :
    Measure ((Langlands.GeneralLinear (0 + 1) F.Carrier × ((Fin n → F.Carrierˣ) ×
      Langlands.GeneralLinear (n + 1) F.Carrier)) × upperUnipotent (n + 1) F.Carrier) :=
  ((glOneMeasure F n).prod ((tailMeasure F n).prod ((generalLinearHaar F.Carrier n).restrict
    (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier))))).prod (unipotentHaar F.Carrier n)

/-- The point `u · diag(det g / ∏ a, a) · k` of the rearranged parameters. -/
def unfoldedPoint {n : ℕ}
    (x : (Langlands.GeneralLinear (0 + 1) F.Carrier × ((Fin n → F.Carrierˣ) ×
      Langlands.GeneralLinear (n + 1) F.Carrier)) × upperUnipotent (n + 1) F.Carrier) :
    Langlands.GeneralLinear (n + 1) F.Carrier :=
  point ((x.1.1, x.1.2.1), x.2) * x.1.2.2

theorem measurable_unfoldedPoint (n : ℕ) : Measurable (unfoldedPoint F (n := n)) :=
  ((measurable_point F n).comp ((measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk
    measurable_snd)).mul measurable_fst.snd.snd

/-- **Unfolded Iwasawa integration.** Haar measure on `GL_(n+1)` is the pushforward of
`(|det g|⁻ⁿ dg × ω(1, a) da × dk|_K) × du` under `((g, (a, k)), u) ↦ u D(g, a) k`. -/
theorem map_unfoldedMeasure (n : ℕ) :
    Measure.map (unfoldedPoint F (n := n)) (unfoldedMeasure F n) =
      generalLinearHaar F.Carrier n := by
  set dk := (generalLinearHaar F.Carrier n).restrict
    (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier))
  set e : (Langlands.GeneralLinear (0 + 1) F.Carrier × ((Fin n → F.Carrierˣ) ×
      Langlands.GeneralLinear (n + 1) F.Carrier)) × upperUnipotent (n + 1) F.Carrier →
      ((Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
        upperUnipotent (n + 1) F.Carrier) × Langlands.GeneralLinear (n + 1) F.Carrier :=
    fun x => (((x.1.1, x.1.2.1), x.2), x.1.2.2) with he_def
  have he : MeasurePreserving e (unfoldedMeasure F n) ((iwasawaMeasure F n).prod dk) := by
    rw [iwasawaMeasure, parameterMeasure_eq_prod]
    have h1 := (measurePreserving_prodAssoc (glOneMeasure F n) (tailMeasure F n) dk).symm
    have h2 := h1.prod (MeasurePreserving.id (unipotentHaar F.Carrier n))
    have h3 := measurePreserving_prodAssoc ((glOneMeasure F n).prod (tailMeasure F n)) dk
      (unipotentHaar F.Carrier n)
    have h4 := (MeasurePreserving.id ((glOneMeasure F n).prod (tailMeasure F n))).prod
      (Measure.measurePreserving_swap (μ := dk) (ν := unipotentHaar F.Carrier n))
    have h5 := (measurePreserving_prodAssoc ((glOneMeasure F n).prod (tailMeasure F n))
      (unipotentHaar F.Carrier n) dk).symm
    convert h5.comp (h4.comp (h3.comp h2)) using 1
    · funext x
      rfl
    · rfl
  have hπ : Measurable (fun x : ((Langlands.GeneralLinear (0 + 1) F.Carrier ×
      (Fin n → F.Carrierˣ)) × upperUnipotent (n + 1) F.Carrier) ×
        Langlands.GeneralLinear (n + 1) F.Carrier => point x.1 * x.2) :=
    ((measurable_point F n).comp measurable_fst).mul measurable_snd
  rw [show unfoldedPoint F (n := n) = (fun x : ((Langlands.GeneralLinear (0 + 1) F.Carrier ×
      (Fin n → F.Carrierˣ)) × upperUnipotent (n + 1) F.Carrier) ×
        Langlands.GeneralLinear (n + 1) F.Carrier => point x.1 * x.2) ∘ e from rfl,
    ← Measure.map_map hπ he.measurable, he.map_eq, map_iwasawaMeasure_prod]

end Measure

end Langlands.RankinSelberg.RankOneIwasawa
