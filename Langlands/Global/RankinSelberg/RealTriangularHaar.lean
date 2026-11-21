import Langlands.Analysis.Local.CompactFactorizationHaar
import Langlands.Global.RankinSelberg.TriangularDiagonal
import Langlands.Global.RankinSelberg.RealIwasawa
import Langlands.Global.RankinSelberg.RealRankZeroHaar
import Langlands.Group.GL.UpperUnipotentEntryCoordinates

/-! # Real Iwasawa integration with the full diagonal torus -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology
open scoped ENNReal Matrix.Norms.Operator NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean
open Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear
open Langlands.Global.RankinSelbergGlobal
open Langlands.Global.RankinSelbergGlobal.GaugeDescent
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.Archimedean.RealPrincipalSeriesDuality (compactSpace_unitaryCompact)

variable (n : ℕ)
local notation "I" => Fin n
local notation "G" => GeneralLinear n ℝ
local notation "M" => Matrix I I ℝ
local notation "B" => upperTriangularSubgroup n ℝ
local notation "U" => upperUnipotent n ℝ
local notation "D" => I → ℝˣ
local notation "Kc" => unitaryCompact ℝ n

private def diagonalInB : D →* B :=
  (diagonalMatrixUnits ℝ).codRestrict B (fun d => diagonalMatrixUnits_triangular d)

private def unipotentInB : U →* B := Subgroup.inclusion (fun _ hu => hu.1)

@[simp]
private theorem triangularDiagonal_diagonalInB (d : D) :
    triangularDiagonal n ℝ (diagonalInB n d) = d := triangularDiagonal_diagonal d

@[simp]
private theorem triangularDiagonal_unipotentInB (u : U) :
    triangularDiagonal n ℝ (unipotentInB n u) = 1 := by
  funext i
  exact Units.ext (u.property.2 i)

private theorem continuous_diagonalInB : Continuous (diagonalInB n) := by
  apply IsInducing.subtypeVal.continuous_iff.2
  apply Units.continuous_iff.2
  have h (d : D) :
      ((diagonalInB n d : B).val : G).val = Matrix.diagonal (fun i => (d i : ℝ)) := rfl
  have hh : Continuous (fun d : D => ((diagonalInB n d : B).val : G).val) := by
    simp_rw [h]
    exact (continuous_pi fun i => Units.continuous_val.comp (continuous_apply i)).matrix_diagonal
  exact ⟨hh, by
    change Continuous (fun d : D => (((diagonalInB n d : B).val)⁻¹ : G).val)
    simpa only [← Subgroup.coe_inv, ← map_inv, Function.comp_def] using hh.comp continuous_inv⟩

private theorem continuous_unipotentInB : Continuous (unipotentInB n) :=
  IsInducing.subtypeVal.continuous_iff.2 continuous_subtype_val

private def removeTriangularDiagonal (b : B) : U :=
  let c := (diagonalInB n (triangularDiagonal n ℝ b))⁻¹ * b
  ⟨c.val, c.property, fun i => by
    have h : triangularDiagonal n ℝ c = 1 := by
      simp [c]
    exact congrArg (fun d : D => (d i : ℝ)) h⟩

private theorem continuous_removeTriangularDiagonal : Continuous (removeTriangularDiagonal n) := by
  apply IsInducing.subtypeVal.continuous_iff.2
  change Continuous (fun b : B => (((diagonalInB n (triangularDiagonal n ℝ b))⁻¹ * b : B).val))
  exact continuous_subtype_val.comp
    (((continuous_diagonalInB n).comp continuous_triangularDiagonal).inv.mul continuous_id)

/-- The Borel multiplication map with the diagonal factor on the left. -/
def realTriangularCoordinates : (D × U) ≃ₜ B where
  toFun p := diagonalInB n p.1 * unipotentInB n p.2
  invFun b := (triangularDiagonal n ℝ b, removeTriangularDiagonal n b)
  left_inv p := by
    have h : triangularDiagonal n ℝ (diagonalInB n p.1 * unipotentInB n p.2) = p.1 := by simp
    apply Prod.ext h
    apply Subtype.ext
    simp only [removeTriangularDiagonal, h, inv_mul_cancel_left]
    rfl
  right_inv b := by
    apply Subtype.ext
    change (diagonalInB n (triangularDiagonal n ℝ b)).val *
      ((diagonalInB n (triangularDiagonal n ℝ b))⁻¹ * b : B).val = b.val
    rw [← Subgroup.coe_mul, mul_inv_cancel_left]
  continuous_toFun :=
    ((continuous_diagonalInB n).comp continuous_fst).mul
      ((continuous_unipotentInB n).comp continuous_snd)
  continuous_invFun :=
    continuous_triangularDiagonal.prodMk (continuous_removeTriangularDiagonal n)

@[simp]
theorem realTriangularCoordinates_apply (p : D × U) :
    (realTriangularCoordinates n p).val = diagonalMatrixUnits ℝ p.1 * p.2.val := rfl

private def triangularLeftCorrection (b : B) (d : D) : U :=
  ((realTriangularCoordinates n).symm (b * realTriangularCoordinates n (d, 1))).2

private theorem triangularCoordinates_left_mul (b : B) (p : D × U) :
    (realTriangularCoordinates n).symm (b * realTriangularCoordinates n p) =
      (triangularDiagonal n ℝ b * p.1, triangularLeftCorrection n b p.1 * p.2) := by
  have h (d : D) (u : U) : triangularDiagonal n ℝ (b * realTriangularCoordinates n (d, u)) =
      triangularDiagonal n ℝ b * d := by
    change triangularDiagonal n ℝ (b * (diagonalInB n d * unipotentInB n u)) = _
    simp
  obtain ⟨d, u⟩ := p
  apply Prod.ext (h d u)
  apply Subtype.ext
  have h1 := h d 1
  change ((diagonalInB n (triangularDiagonal n ℝ (b * realTriangularCoordinates n (d, u))))⁻¹ *
      (b * realTriangularCoordinates n (d, u)) : B).val =
    ((diagonalInB n (triangularDiagonal n ℝ (b * realTriangularCoordinates n (d, 1))))⁻¹ *
      (b * realTriangularCoordinates n (d, 1)) : B).val * u.val
  rw [h d u, h1]
  change _ = (_ : B).val * (unipotentInB n u).val
  rw [← Subgroup.coe_mul]
  congr 1
  change _ * (b * (diagonalInB n d * unipotentInB n u)) =
    (_ * (b * (diagonalInB n d * unipotentInB n 1))) * unipotentInB n u
  rw [map_one, mul_one]
  group

local instance realTriangularMatrixSecondCountable : SecondCountableTopology M :=
  inferInstanceAs (SecondCountableTopology (I → I → ℝ))
local instance realTriangularGLSecondCountable : SecondCountableTopology G :=
  (show IsOpenEmbedding (Units.val : G → M) from Units.isOpenEmbedding_val).isInducing.secondCountableTopology
local instance realTriangularUnitsSecondCountable : SecondCountableTopology (ℝˣ) :=
  (show IsEmbedding (Units.val : ℝˣ → ℝ) from Units.isEmbedding_val₀).isInducing.secondCountableTopology
local instance realTriangularGLMeasurable : MeasurableSpace G := borel _
local instance realTriangularGLBorel : BorelSpace G := ⟨rfl⟩
local instance realTriangularUnitsMeasurable : MeasurableSpace (ℝˣ) := borel _
local instance realTriangularUnitsBorel : BorelSpace (ℝˣ) := ⟨rfl⟩

private theorem realTriangularCoordinates_map_isHaar
    (μD : Measure D) [μD.IsHaarMeasure] [SFinite μD]
    (μU : Measure U) [μU.IsHaarMeasure] [SFinite μU] :
    ((μD.prod μU).map (realTriangularCoordinates n)).IsHaarMeasure := by
  let e := realTriangularCoordinates n
  let μB := (μD.prod μU).map e
  have he : Measurable (e : D × U → B) := e.continuous.measurable
  let : IsFiniteMeasureOnCompacts μB := IsFiniteMeasureOnCompacts.map (μD.prod μU) e
  let : IsOpenPosMeasure μB := e.continuous.isOpenPosMeasure_map e.surjective
  refine { map_mul_left_eq_self := fun b => ?_ }
  have hc : Continuous (triangularLeftCorrection n b) :=
    continuous_snd.comp (e.symm.continuous.comp (continuous_const.mul
      (e.continuous.comp (continuous_id.prodMk continuous_const))))
  have hm : Measurable (fun p : D × U => triangularLeftCorrection n b p.1 * p.2) :=
    ((hc.comp continuous_fst).mul continuous_snd).measurable
  have ht := (measurePreserving_mul_left μD (triangularDiagonal n ℝ b)).skew_product
    hm (Filter.Eventually.of_forall fun d =>
      (measurePreserving_mul_left μU (triangularLeftCorrection n b d)).map_eq)
  have hmul : Measurable (fun c : B => b * c) := (continuous_const.mul continuous_id).measurable
  have hfun : (fun c : B => b * c) ∘ e =
      e ∘ (fun p : D × U => (triangularDiagonal n ℝ b * p.1,
        triangularLeftCorrection n b p.1 * p.2)) := by
    funext p
    exact (e.apply_symm_apply (b * e p)).symm.trans
      (congrArg e (triangularCoordinates_left_mul n b p))
  change μB.map (fun c : B => b * c) = μB
  dsimp only [μB]
  rw [Measure.map_map hmul he, hfun, ← Measure.map_map he ht.measurable, ht.map_eq]

private theorem exists_haar_eq_triangular (μ : Measure G) [μ.IsHaarMeasure]
    (μD : Measure D) [μD.IsHaarMeasure] [SFinite μD]
    (μU : Measure U) [μU.IsHaarMeasure] [SFinite μU]
    (μK : Measure Kc) [μK.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ μ =
      c • (((μD.prod μU).prod μK).map
        (fun p : (D × U) × Kc => diagonalMatrixUnits ℝ p.1.1 * p.1.2.val * p.2.val)) := by
  let : LocallyCompactSpace M := inferInstanceAs (LocallyCompactSpace (I → I → ℝ))
  let : LocallyCompactSpace G :=
    (show IsOpenEmbedding (Units.val : G → M) from Units.isOpenEmbedding_val).locallyCompactSpace
  let e := realTriangularCoordinates n
  let μB := (μD.prod μU).map e
  let : μB.IsHaarMeasure := realTriangularCoordinates_map_isHaar n μD μU
  have hBK (g : G) : ∃ b ∈ B, ∃ k ∈ Kc, g = b * k := by
    let q := RealIwasawa.bpart g
    refine ⟨q, (RealIwasawa.isPosUpper_bpart g).1, (RealIwasawa.kpart g).val,
      (RealIwasawa.kpart g).property, (RealIwasawa.bpart_mul_kpart g).symm⟩
  obtain ⟨c, hc, he⟩ := CompactFactorization.exists_pos_eq_smul_map_mul_prod
    μ B isClosed_upperTriangular Kc (isCompact_iff_compactSpace.mpr (compactSpace_unitaryCompact n))
    hBK μB μK
  refine ⟨c, hc, ?_⟩
  have hmap : Measurable (fun p : B × Kc => p.1.val * p.2.val) :=
    (measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  have heMap : μB.prod μK = ((μD.prod μU).prod μK).map (Prod.map e id) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map (μD.prod μU) μK e.continuous.measurable (measurable_id (α := Kc)))
  rw [he]
  rw [heMap, Measure.map_map hmap (e.continuous.measurable.prodMap measurable_id)]
  rfl

/-- Coordinatewise multiplicative Haar measure `∏(dtᵢ/|tᵢ|)` on the full real torus. -/
def realDiagonalHaar : Measure D := Measure.pi fun _ : I => RealRankZero.unitsHaar

local instance : SigmaFinite RealRankZero.unitsHaar := inferInstance
local instance : (realDiagonalHaar n).IsHaarMeasure := by unfold realDiagonalHaar; infer_instance
local instance : SigmaFinite (realDiagonalHaar n) := by unfold realDiagonalHaar; infer_instance

/-- The canonical full diagonal and upper-unipotent coordinate measure pushes to a left Haar
measure up to scale, with any orthogonal-group Haar measure. -/
def RealTriangularHaarStatement : Prop :=
  ∀ (μ : Measure G) (ν : AdditiveHaarMeasure ℝ) (κ : Measure Kc),
    μ.IsHaarMeasure → κ.IsHaarMeasure →
    ∃ c : ℝ≥0, 0 < c ∧ μ = c • (((realDiagonalHaar n).prod
      (upperEntryProductMeasure ν n)).prod κ).map
        (fun p : (D × (UpperEntryPair n → ℝ)) × Kc =>
          diagonalMatrixUnits ℝ p.1.1 * ((upperEntryCoordinates n).symm p.1.2).val * p.2.val)

theorem realTriangularHaar : RealTriangularHaarStatement n := by
  intro μ ν κ hμ hκ
  let : μ.IsHaarMeasure := hμ
  let : κ.IsHaarMeasure := hκ
  let : SigmaFinite ν.measure := by
    let : ν.measure.IsAddHaarMeasure := ν.isAddHaar
    infer_instance
  let e := (upperEntryCoordinates n (K := ℝ)).symm
  let μU := (upperEntryProductMeasure ν n).map e
  let : μU.IsHaarMeasure := upperEntryProductMeasure_isHaar ν
  let : SFinite μU := inferInstanceAs (SFinite ((upperEntryProductMeasure ν n).map e))
  obtain ⟨c, hc, he⟩ := exists_haar_eq_triangular n μ (realDiagonalHaar n) μU κ
  refine ⟨c, hc, ?_⟩
  let η := ((realDiagonalHaar n).prod (upperEntryProductMeasure ν n)).prod κ
  let T : (D × (UpperEntryPair n → ℝ)) × Kc → (D × U) × Kc := Prod.map (Prod.map id e) id
  let q : (D × U) × Kc → G := fun p => diagonalMatrixUnits ℝ p.1.1 * p.1.2.val * p.2.val
  have hmT : Measurable T := (measurable_id.prodMap e.measurable).prodMap measurable_id
  have hd : Measurable (diagonalMatrixUnits ℝ : D → G) :=
    (continuous_subtype_val.comp (continuous_diagonalInB n)).measurable
  have hq : Measurable q := ((hd.comp measurable_fst.fst).mul
    (measurable_subtype_coe.comp measurable_fst.snd)).mul
    (measurable_subtype_coe.comp measurable_snd)
  have hT : η.map T = ((realDiagonalHaar n).prod μU).prod κ := by
    dsimp only [η, T, μU]
    rw [← Measure.map_prod_map _ _ (measurable_id.prodMap e.measurable) measurable_id,
      ← Measure.map_prod_map _ _ measurable_id e.measurable, Measure.map_id, Measure.map_id]
  change μ = c • Measure.map q (((realDiagonalHaar n).prod μU).prod κ) at he
  rw [he, ← hT, Measure.map_map hq hmT]
  rfl

end Langlands.GodementJacquet
