import Langlands.Global.RankinSelberg.RealIwasawa
import Langlands.Group.GL.UpperUnipotentEntryCoordinates
import Langlands.Analysis.Local.CompactFactorizationHaar

/-! # Haar measure in the positive diagonal, unipotent and orthogonal coordinates -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Matrix.Norms.Operator NNReal

namespace Langlands.Global.RankinSelbergGlobal.RealLocalIwasawaHaar

open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.Archimedean.RealPrincipalSeriesDuality (compactSpace_unitaryCompact)
open RealIwasawa

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance iwasawaGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) :=
  borel _
local instance iwasawaGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
local instance iwasawaGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "N" => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "K" => unitaryCompact ℝ n
local notation "Y" => (Fin n → ℝ)

private def triangular (x : Y × N) : G := torus x.1 * (x.2 : G)

private theorem triangular_reorder (x : Y × N) :
    triangular x = (conjTorus x.1 x.2 : G) * torus x.1 := by
  change torus x.1 * (x.2 : G) = (torus x.1 * (x.2 : G) * torus (-x.1)) * torus x.1
  rw [torus_neg, inv_mul_cancel_right]

private theorem kpart_triangular (x : Y × N) : kpart (triangular x) = 1 := by
  rw [triangular_reorder]
  simpa only [OneMemClass.coe_one, mul_one] using kpart_iwasawa (conjTorus x.1 x.2) x.1 (1 : K)

private theorem alpha_triangular (x : Y × N) : alpha (triangular x) = x.1 := by
  rw [triangular_reorder]
  simpa only [OneMemClass.coe_one, mul_one] using alpha_iwasawa (conjTorus x.1 x.2) x.1 (1 : K)

private theorem triangular_coordinates {g : G} (hg : kpart g = 1) :
    triangular (alpha g, conjTorus (-alpha g) (npart g)) = g := by
  calc
    _ = (npart g : G) * torus (alpha g) := by
      change torus (alpha g) * (torus (-alpha g) * (npart g : G) * torus (-(-alpha g))) = _
      simp only [torus_neg, inv_inv]
      group
    _ = g := by simpa only [hg, OneMemClass.coe_one, mul_one] using
          npart_mul_torus_mul_kpart g

private def triangularShift (q x : Y × N) : Y × N :=
  (q.1 + x.1, conjTorus (-x.1) q.2 * x.2)

private theorem triangular_shift (q x : Y × N) :
    triangular (triangularShift q x) = triangular q * triangular x := by
  change torus (q.1 + x.1) * (torus (-x.1) * (q.2 : G) * torus (-(-x.1)) * (x.2 : G)) = _
  simp only [triangular, torus_add, torus_neg, inv_inv]
  group

private theorem triangular_inv (x : Y × N) :
    triangular (-x.1, conjTorus x.1 x.2⁻¹) = (triangular x)⁻¹ := by
  change torus (-x.1) * (torus x.1 * (x.2 : G)⁻¹ * torus (-x.1)) = _
  simp only [triangular, torus_neg, mul_inv_rev]
  group

/-- The closed subgroup of positive-diagonal upper triangular matrices. -/
private def positiveTriangular (n : ℕ) : Subgroup (Langlands.GeneralLinear n ℝ) where
  carrier := {g | kpart g = 1}
  one_mem' := by
    change kpart (1 : Langlands.GeneralLinear n ℝ) = 1
    simpa only [triangular, torus_zero, OneMemClass.coe_one, mul_one] using
      kpart_triangular ((0 : Fin n → ℝ), (1 : Langlands.GeneralLinear.upperUnipotent n ℝ))
  mul_mem' {g h} hg hh := by
    change kpart (g * h) = 1
    rw [← triangular_coordinates hg, ← triangular_coordinates hh, ← triangular_shift]
    exact kpart_triangular _
  inv_mem' {g} hg := by
    change kpart g⁻¹ = 1
    rw [← triangular_coordinates hg, ← triangular_inv]
    exact kpart_triangular _

private theorem isClosed_positiveTriangular (n : ℕ) :
    IsClosed (positiveTriangular n : Set (Langlands.GeneralLinear n ℝ)) :=
  isClosed_eq continuous_kpart continuous_const

private theorem continuous_triangular : Continuous (triangular (n := n)) :=
  (continuous_torus.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

private theorem unipotent_coordinate_mem (g : positiveTriangular n) :
    (torus (alpha (g : G)))⁻¹ * (g : G) ∈ N := by
  have h : (torus (alpha (g : G)))⁻¹ * (g : G) =
      (conjTorus (-alpha (g : G)) (npart (g : G)) : G) := by
    calc
      _ = (torus (alpha (g : G)))⁻¹ *
          triangular (alpha (g : G), conjTorus (-alpha (g : G)) (npart (g : G))) :=
        congrArg ((torus (alpha (g : G)))⁻¹ * ·) (triangular_coordinates g.2).symm
      _ = _ := by rw [triangular, inv_mul_cancel_left]
  rw [h]
  exact Subtype.prop _

private def triangularHomeomorph (n : ℕ) :
    ((Fin n → ℝ) × Langlands.GeneralLinear.upperUnipotent n ℝ) ≃ₜ positiveTriangular n where
  toFun x := ⟨triangular x, kpart_triangular x⟩
  invFun g := (alpha g.val, ⟨(torus (alpha g.val))⁻¹ * g.val, unipotent_coordinate_mem g⟩)
  left_inv x := by
    apply Prod.ext
    · exact alpha_triangular x
    · apply Subtype.ext
      change (torus (alpha (triangular x)))⁻¹ * triangular x = x.2.val
      rw [alpha_triangular, triangular, inv_mul_cancel_left]
  right_inv g := by
    apply Subtype.ext
    change torus (alpha g.val) * ((torus (alpha g.val))⁻¹ * g.val) = g.val
    exact mul_inv_cancel_left _ _
  continuous_toFun := continuous_triangular.subtype_mk _
  continuous_invFun := by
    have h : Continuous (fun g : positiveTriangular n => alpha g.val) :=
      continuous_alpha.comp continuous_subtype_val
    exact h.prodMk (((continuous_torus.comp h).inv.mul continuous_subtype_val).subtype_mk _)

private theorem continuous_triangularShift_snd (q : Y × N) :
    Continuous (fun x : Y × N => (triangularShift q x).2) := by
  apply Continuous.subtype_mk
  change Continuous (fun x : Y × N => torus (-x.1) * (q.2 : G) * torus (-(-x.1)) * (x.2 : G))
  simp only [torus_neg, inv_inv]
  have h : Continuous (fun x : Y × N => torus x.1) := continuous_torus.comp continuous_fst
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

/-- Left Haar measure on the real general linear group in positive diagonal, upper
unipotent, orthogonal order. The diagonal coordinates are the logarithms of the positive entries. -/
def RealIwasawaHaarStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (Langlands.GeneralLinear n ℝ))
    (ν : Measure (Langlands.GeneralLinear.upperUnipotent n ℝ))
    (κ : Measure (unitaryCompact ℝ n)), μ.IsHaarMeasure → ν.IsHaarMeasure → κ.IsHaarMeasure →
    ∃ c : ℝ≥0, 0 < c ∧ μ = c • Measure.map
      (fun x : ((Fin n → ℝ) × Langlands.GeneralLinear.upperUnipotent n ℝ) ×
          unitaryCompact ℝ n => torus x.1.1 * x.1.2.val * x.2.val)
      ((volume.prod ν).prod κ)

theorem realIwasawaHaar : RealIwasawaHaarStatement := by
  intro n μ ν κ hμ hν hκ
  let : μ.IsHaarMeasure := hμ
  let : ν.IsHaarMeasure := hν
  let : κ.IsHaarMeasure := hκ
  let : LocallyCompactSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) :=
    Langlands.GeneralLinear.UpperUnipotent.locallyCompactSpace
  let : SecondCountableTopology (Langlands.GeneralLinear.upperUnipotent n ℝ) :=
    inferInstanceAs (SecondCountableTopology
      (Langlands.GeneralLinear.upperUnipotent n ℝ : Set (Langlands.GeneralLinear n ℝ)))
  let : SigmaFinite ν := inferInstance
  let e := triangularHomeomorph n
  let σ := (volume.prod ν).map e
  let : σ.IsHaarMeasure := triangularHaar_isHaar ν
  have hfac (g : Langlands.GeneralLinear n ℝ) :
      ∃ p ∈ positiveTriangular n, ∃ k ∈ unitaryCompact ℝ n, g = p * k := by
    refine ⟨(npart g).val * torus (alpha g), ?_, (kpart g).val, (kpart g).2,
      (npart_mul_torus_mul_kpart g).symm⟩
    change kpart ((npart g).val * torus (alpha g)) = 1
    simpa only [OneMemClass.coe_one, mul_one] using kpart_iwasawa (npart g) (alpha g) (1 : unitaryCompact ℝ n)
  obtain ⟨c, hc, hEq⟩ := Langlands.CompactFactorization.exists_pos_eq_smul_map_mul_prod
    μ (positiveTriangular n) (isClosed_positiveTriangular n)
    (unitaryCompact ℝ n) (isCompact_iff_compactSpace.mpr (compactSpace_unitaryCompact n)) hfac σ κ
  refine ⟨c, hc, ?_⟩
  rw [hEq]
  have hprod : σ.prod κ = Measure.map (Prod.map e id) ((volume.prod ν).prod κ) := by
    rw [← Measure.map_prod_map _ _ e.measurable measurable_id, Measure.map_id]
  have hm : Measurable (fun p : positiveTriangular n × unitaryCompact ℝ n => p.1.val * p.2.val) :=
    (measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  rw [hprod, Measure.map_map hm (e.measurable.prodMap measurable_id)]
  rfl

private def scalarLebesgue : Langlands.HarmonicAnalysis.AdditiveHaarMeasure ℝ where
  measure := volume
  isAddHaar := inferInstance
  regular := inferInstance

local instance : SigmaFinite scalarLebesgue.measure :=
  inferInstanceAs (SigmaFinite (volume : Measure ℝ))

/-- The real Iwasawa chart in log diagonal coordinates and the strictly upper entries of the
unit-diagonal factor. -/
def RealIwasawaHaarEntriesStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (Langlands.GeneralLinear n ℝ)) (κ : Measure (unitaryCompact ℝ n)),
    μ.IsHaarMeasure → κ.IsHaarMeasure →
    ∃ c : ℝ≥0, 0 < c ∧ μ = c • Measure.map
      (fun p : ((Fin n → ℝ) × (UpperEntryPair n → ℝ)) × unitaryCompact ℝ n =>
        torus p.1.1 * ((upperEntryCoordinates n).symm p.1.2).val * p.2.val)
      ((volume.prod volume).prod κ)

theorem realIwasawaHaarEntries : RealIwasawaHaarEntriesStatement := by
  intro m μ κ hμ hκ
  let : κ.IsHaarMeasure := hκ
  let e : upperUnipotent m ℝ ≃ₜ (UpperEntryPair m → ℝ) := upperEntryCoordinates m
  let ν : Measure (upperUnipotent m ℝ) := (volume : Measure (UpperEntryPair m → ℝ)).map e.symm
  have hν : ν.IsHaarMeasure := upperEntryProductMeasure_isHaar (d := m) scalarLebesgue
  obtain ⟨c, hc, hEq⟩ := realIwasawaHaar m μ ν κ hμ hν hκ
  let η := ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (UpperEntryPair m → ℝ))).prod κ
  let T : ((Fin m → ℝ) × (UpperEntryPair m → ℝ)) × unitaryCompact ℝ m →
      ((Fin m → ℝ) × upperUnipotent m ℝ) × unitaryCompact ℝ m := Prod.map (Prod.map id e.symm) id
  let q : ((Fin m → ℝ) × upperUnipotent m ℝ) × unitaryCompact ℝ m → Langlands.GeneralLinear m ℝ :=
    fun p => torus p.1.1 * p.1.2.val * p.2.val
  have hmT : Measurable T := (measurable_id.prodMap e.symm.measurable).prodMap measurable_id
  have hq : Measurable q :=
    ((continuous_torus.measurable.comp (measurable_fst.comp measurable_fst)).mul
      (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst))).mul
      (measurable_subtype_coe.comp measurable_snd)
  have hT : η.map T = ((volume : Measure (Fin m → ℝ)).prod ν).prod κ := by
    change (((volume : Measure (Fin m → ℝ)).prod (volume : Measure (UpperEntryPair m → ℝ))).prod κ).map
      (Prod.map (Prod.map id e.symm) id) = _
    rw [← Measure.map_prod_map _ _ (measurable_id.prodMap e.symm.measurable) measurable_id,
      ← Measure.map_prod_map _ _ measurable_id e.symm.measurable, Measure.map_id, Measure.map_id]
  refine ⟨c, hc, ?_⟩
  change μ = c • Measure.map q ((volume.prod ν).prod κ) at hEq
  rw [hEq, ← hT, Measure.map_map hq hmT]
  rfl

/-- The Haar pushforward formula, in both group and additive entry coordinates. -/
def RealIwasawaHaarChartStatement : Prop := RealIwasawaHaarStatement ∧ RealIwasawaHaarEntriesStatement

theorem realIwasawaHaarChart : RealIwasawaHaarChartStatement :=
  ⟨realIwasawaHaar, realIwasawaHaarEntries⟩

end Langlands.Global.RankinSelbergGlobal.RealLocalIwasawaHaar
