import Langlands.Global.RankinSelberg.ComplexLocalIwasawa
import Langlands.Analysis.Local.CompactFactorizationHaar

/-! # Haar measure in the positive diagonal, unipotent and unitary coordinates -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Matrix.Norms.Operator NNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexLocalIwasawaHaar

open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.Archimedean.ComplexDuality (isCompact_unitaryCompact)
open ComplexLocalIwasawa
open ComplexLocalWhittakerGauge (logTorus)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance iwasawaGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) :=
  borel _
local instance iwasawaGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩
local instance iwasawaGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Y" => (Fin n → ℝ)

private theorem logTorus_zero : logTorus (0 : Y) = 1 := by
  apply Units.ext
  simp [ComplexLocalWhittakerGauge.logTorus_val, ← Matrix.diagonal_one]

private def triangular (x : Y × N) : G := logTorus x.1 * (x.2 : G)

private theorem triangular_reorder (x : Y × N) :
    triangular x = (conjTorus x.1 x.2 : G) * logTorus x.1 := by
  rw [triangular, conjTorus_val, inv_mul_cancel_right]

private theorem kpart_triangular (x : Y × N) : kpart (triangular x) = 1 := by
  rw [triangular_reorder]
  simpa only [OneMemClass.coe_one, mul_one] using kpart_iwasawa (conjTorus x.1 x.2) x.1 (1 : K)

private theorem alpha_triangular (x : Y × N) : alpha (triangular x) = x.1 := by
  rw [triangular_reorder]
  simpa only [OneMemClass.coe_one, mul_one] using alpha_iwasawa (conjTorus x.1 x.2) x.1 (1 : K)

private theorem triangular_coordinates {g : G} (hg : kpart g = 1) :
    triangular (alpha g, conjTorus (-alpha g) (npart g)) = g := by
  calc
    _ = (npart g : G) * logTorus (alpha g) := by
      simp only [triangular, conjTorus_val, logTorus_neg, inv_inv]
      group
    _ = g := by simpa only [hg, OneMemClass.coe_one, mul_one] using
          npart_mul_logTorus_mul_kpart g

private def triangularShift (q x : Y × N) : Y × N :=
  (q.1 + x.1, conjTorus (-x.1) q.2 * x.2)

private theorem triangular_shift (q x : Y × N) :
    triangular (triangularShift q x) = triangular q * triangular x := by
  simp only [triangularShift, triangular, logTorus_add, Subgroup.coe_mul, conjTorus_val,
    logTorus_neg, inv_inv]
  group

private theorem triangular_inv (x : Y × N) :
    triangular (-x.1, conjTorus x.1 x.2⁻¹) = (triangular x)⁻¹ := by
  simp only [triangular, logTorus_neg, conjTorus_val, Subgroup.coe_inv, mul_inv_rev]
  group

/-- The closed subgroup of positive-diagonal upper triangular matrices. -/
private def positiveTriangular (n : ℕ) : Subgroup (Langlands.GeneralLinear n ℂ) where
  carrier := {g | kpart g = 1}
  one_mem' := by
    change kpart (1 : Langlands.GeneralLinear n ℂ) = 1
    simpa only [triangular, logTorus_zero, OneMemClass.coe_one, mul_one] using
      kpart_triangular ((0 : Fin n → ℝ), (1 : Langlands.GeneralLinear.upperUnipotent n ℂ))
  mul_mem' {g h} hg hh := by
    change kpart (g * h) = 1
    rw [← triangular_coordinates hg, ← triangular_coordinates hh, ← triangular_shift]
    exact kpart_triangular _
  inv_mem' {g} hg := by
    change kpart g⁻¹ = 1
    rw [← triangular_coordinates hg, ← triangular_inv]
    exact kpart_triangular _

private theorem isClosed_positiveTriangular (n : ℕ) :
    IsClosed (positiveTriangular n : Set (Langlands.GeneralLinear n ℂ)) :=
  isClosed_eq continuous_kpart continuous_const

private theorem continuous_triangular : Continuous (triangular (n := n)) :=
  (continuous_logTorus.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

private theorem unipotent_coordinate_mem (g : positiveTriangular n) :
    (logTorus (alpha (g : G)))⁻¹ * (g : G) ∈ N := by
  have h : (logTorus (alpha (g : G)))⁻¹ * (g : G) =
      (conjTorus (-alpha (g : G)) (npart (g : G)) : G) := by
    calc
      _ = (logTorus (alpha (g : G)))⁻¹ *
          triangular (alpha (g : G), conjTorus (-alpha (g : G)) (npart (g : G))) :=
        congrArg ((logTorus (alpha (g : G)))⁻¹ * ·) (triangular_coordinates g.2).symm
      _ = _ := by rw [triangular, inv_mul_cancel_left]
  rw [h]
  exact Subtype.prop _

private def triangularHomeomorph (n : ℕ) :
    ((Fin n → ℝ) × Langlands.GeneralLinear.upperUnipotent n ℂ) ≃ₜ positiveTriangular n where
  toFun x := ⟨triangular x, kpart_triangular x⟩
  invFun g := (alpha g.val, ⟨(logTorus (alpha g.val))⁻¹ * g.val, unipotent_coordinate_mem g⟩)
  left_inv x := by
    apply Prod.ext
    · exact alpha_triangular x
    · apply Subtype.ext
      change (logTorus (alpha (triangular x)))⁻¹ * triangular x = x.2.val
      rw [alpha_triangular, triangular, inv_mul_cancel_left]
  right_inv g := by
    apply Subtype.ext
    change logTorus (alpha g.val) * ((logTorus (alpha g.val))⁻¹ * g.val) = g.val
    exact mul_inv_cancel_left _ _
  continuous_toFun := continuous_triangular.subtype_mk _
  continuous_invFun := by
    have h : Continuous (fun g : positiveTriangular n => alpha g.val) :=
      continuous_alpha.comp continuous_subtype_val
    exact h.prodMk (((continuous_logTorus.comp h).inv.mul continuous_subtype_val).subtype_mk _)

private theorem continuous_triangularShift_snd (q : Y × N) :
    Continuous (fun x : Y × N => (triangularShift q x).2) := by
  apply Continuous.subtype_mk
  simp only [conjTorus_val, logTorus_neg, inv_inv]
  have h : Continuous (fun x : Y × N => logTorus x.1) := continuous_logTorus.comp continuous_fst
  exact ((h.inv.mul continuous_const).mul h).mul (continuous_subtype_val.comp continuous_snd)

private theorem triangularHaar_isHaar (ν : Measure N) [ν.IsHaarMeasure] [SigmaFinite ν] :
    ((volume.prod ν).map (triangularHomeomorph n)).IsHaarMeasure := by
  let e := triangularHomeomorph n
  let σ := (volume.prod ν).map e
  have : IsFiniteMeasureOnCompacts σ := IsFiniteMeasureOnCompacts.map _ e
  have : IsOpenPosMeasure σ := e.continuous.isOpenPosMeasure_map e.surjective
  refine { map_mul_left_eq_self := fun p => ?_ }
  let q := e.symm p
  have heq : (p * ·) ∘ e = e ∘ triangularShift q := by
    funext x
    apply Subtype.ext
    change (p : G) * triangular x = triangular (triangularShift q x)
    rw [triangular_shift]
    exact congrArg (fun t : positiveTriangular n => (t : G) * triangular x) (e.apply_symm_apply p).symm
  have hy : MeasurePreserving (q.1 + ·) (volume : Measure Y) volume :=
    measurePreserving_add_left volume q.1
  have hp : MeasurePreserving (triangularShift q) (volume.prod ν) (volume.prod ν) :=
    hy.skew_product (continuous_triangularShift_snd q).measurable
      (Filter.Eventually.of_forall fun y => map_mul_left_eq_self ν (conjTorus (-y) q.2))
  change Measure.map (p * ·) σ = σ
  rw [show σ = (volume.prod ν).map e from rfl, Measure.map_map (measurable_const_mul _) e.measurable,
    heq, ← Measure.map_map e.measurable hp.measurable, hp.map_eq]

/-- Left Haar measure on the complex general linear group in positive diagonal, upper
unipotent, unitary order. The diagonal coordinates are the logarithms of the real entries. -/
def ComplexIwasawaHaarStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (Langlands.GeneralLinear n ℂ))
    (ν : Measure (Langlands.GeneralLinear.upperUnipotent n ℂ))
    (κ : Measure (unitaryCompact ℂ n)), μ.IsHaarMeasure → ν.IsHaarMeasure → κ.IsHaarMeasure →
    ∃ c : ℝ≥0, 0 < c ∧ μ = c • Measure.map
      (fun x : ((Fin n → ℝ) × Langlands.GeneralLinear.upperUnipotent n ℂ) ×
          unitaryCompact ℂ n => logTorus x.1.1 * x.1.2.val * x.2.val)
      ((volume.prod ν).prod κ)

theorem complexIwasawaHaar : ComplexIwasawaHaarStatement := by
  intro n μ ν κ hμ hν hκ
  let : μ.IsHaarMeasure := hμ
  let : ν.IsHaarMeasure := hν
  let : κ.IsHaarMeasure := hκ
  let : LocallyCompactSpace (Langlands.GeneralLinear.upperUnipotent n ℂ) :=
    Langlands.GeneralLinear.UpperUnipotent.locallyCompactSpace
  let : SecondCountableTopology (Langlands.GeneralLinear.upperUnipotent n ℂ) :=
    inferInstanceAs (SecondCountableTopology
      (Langlands.GeneralLinear.upperUnipotent n ℂ : Set (Langlands.GeneralLinear n ℂ)))
  let : SigmaFinite ν := inferInstance
  let e := triangularHomeomorph n
  let σ := (volume.prod ν).map e
  let : σ.IsHaarMeasure := triangularHaar_isHaar ν
  have hfac (g : Langlands.GeneralLinear n ℂ) :
      ∃ p ∈ positiveTriangular n, ∃ k ∈ unitaryCompact ℂ n, g = p * k := by
    obtain ⟨u, y, k, hk⟩ := exists_iwasawa g
    refine ⟨u.val * logTorus y, ?_, k.val, k.2, hk⟩
    change kpart (u.val * logTorus y) = 1
    simpa only [OneMemClass.coe_one, mul_one] using kpart_iwasawa u y (1 : unitaryCompact ℂ n)
  obtain ⟨c, hc, hEq⟩ := Langlands.CompactFactorization.exists_pos_eq_smul_map_mul_prod
    μ (positiveTriangular n) (isClosed_positiveTriangular n)
    (unitaryCompact ℂ n) (isCompact_unitaryCompact n) hfac σ κ
  refine ⟨c, hc, ?_⟩
  rw [hEq]
  have hprod : σ.prod κ = Measure.map (Prod.map e id) ((volume.prod ν).prod κ) := by
    rw [← Measure.map_prod_map _ _ e.measurable measurable_id, Measure.map_id]
  have hm : Measurable (fun p : positiveTriangular n × unitaryCompact ℂ n => p.1.val * p.2.val) :=
    (measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  rw [hprod, Measure.map_map hm (e.measurable.prodMap measurable_id)]
  rfl

end Langlands.Global.RankinSelbergGlobal.ComplexLocalIwasawaHaar
