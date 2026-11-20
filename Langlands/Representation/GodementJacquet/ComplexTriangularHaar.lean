import Langlands.Analysis.Local.CompactFactorizationHaar
import Langlands.Global.RankinSelberg.TriangularDiagonal
import Langlands.Representation.Archimedean.ComplexDuality.GramWeight
import Langlands.Representation.Archimedean.ComplexDuality.UnitaryHaar
import Langlands.Representation.GodementJacquet.ComplexMatrixHaar
import Langlands.Group.GL.UpperUnipotentEntryCoordinates

/-! # Complex Iwasawa integration in diagonal-then-unipotent coordinates -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology
open scoped ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean
open Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear
open Langlands.Global.RankinSelbergGlobal.GaugeDescent

variable (n : ℕ)
local notation "I" => Fin n
local notation "G" => GeneralLinear n ℂ
local notation "M" => Matrix I I ℂ
local notation "B" => upperTriangularSubgroup n ℂ
local notation "U" => upperUnipotent n ℂ
local notation "D" => I → ℂˣ
local notation "Kc" => unitaryCompact ℂ n

private def diagonalInB : D →* B :=
  (diagonalMatrixUnits ℂ).codRestrict B (fun d => diagonalMatrixUnits_triangular d)

private def unipotentInB : U →* B := Subgroup.inclusion (fun _ hu => hu.1)

@[simp]
private theorem triangularDiagonal_diagonalInB (d : D) :
    triangularDiagonal n ℂ (diagonalInB n d) = d := triangularDiagonal_diagonal d

@[simp]
private theorem triangularDiagonal_unipotentInB (u : U) :
    triangularDiagonal n ℂ (unipotentInB n u) = 1 := by
  funext i
  exact Units.ext (u.property.2 i)

private theorem continuous_diagonalInB : Continuous (diagonalInB n) := by
  apply IsInducing.subtypeVal.continuous_iff.2
  apply Units.continuous_iff.2
  have h (d : D) :
      ((diagonalInB n d : B).val : G).val = Matrix.diagonal (fun i => (d i : ℂ)) := rfl
  have hh : Continuous (fun d : D => ((diagonalInB n d : B).val : G).val) := by
    simp_rw [h]
    exact (continuous_pi fun i => Units.continuous_val.comp (continuous_apply i)).matrix_diagonal
  exact ⟨hh, by
    change Continuous (fun d : D => (((diagonalInB n d : B).val)⁻¹ : G).val)
    simpa only [← Subgroup.coe_inv, ← map_inv, Function.comp_def] using hh.comp continuous_inv⟩

private theorem continuous_unipotentInB : Continuous (unipotentInB n) :=
  IsInducing.subtypeVal.continuous_iff.2 continuous_subtype_val

private def removeTriangularDiagonal (b : B) : U :=
  let c := (diagonalInB n (triangularDiagonal n ℂ b))⁻¹ * b
  ⟨c.val, c.property, fun i => by
    have h : triangularDiagonal n ℂ c = 1 := by
      simp [c]
    exact congrArg (fun d : D => (d i : ℂ)) h⟩

private theorem continuous_removeTriangularDiagonal : Continuous (removeTriangularDiagonal n) := by
  apply IsInducing.subtypeVal.continuous_iff.2
  change Continuous (fun b : B => (((diagonalInB n (triangularDiagonal n ℂ b))⁻¹ * b : B).val))
  exact continuous_subtype_val.comp
    (((continuous_diagonalInB n).comp continuous_triangularDiagonal).inv.mul continuous_id)

/-- The Borel multiplication map with the diagonal factor on the left. -/
def complexTriangularCoordinates : (D × U) ≃ₜ B where
  toFun p := diagonalInB n p.1 * unipotentInB n p.2
  invFun b := (triangularDiagonal n ℂ b, removeTriangularDiagonal n b)
  left_inv p := by
    have h : triangularDiagonal n ℂ (diagonalInB n p.1 * unipotentInB n p.2) = p.1 := by simp
    apply Prod.ext h
    apply Subtype.ext
    simp only [removeTriangularDiagonal, h, inv_mul_cancel_left]
    rfl
  right_inv b := by
    apply Subtype.ext
    change (diagonalInB n (triangularDiagonal n ℂ b)).val *
      ((diagonalInB n (triangularDiagonal n ℂ b))⁻¹ * b : B).val = b.val
    rw [← Subgroup.coe_mul, mul_inv_cancel_left]
  continuous_toFun :=
    ((continuous_diagonalInB n).comp continuous_fst).mul
      ((continuous_unipotentInB n).comp continuous_snd)
  continuous_invFun :=
    continuous_triangularDiagonal.prodMk (continuous_removeTriangularDiagonal n)

@[simp]
theorem complexTriangularCoordinates_apply (p : D × U) :
    (complexTriangularCoordinates n p).val = diagonalMatrixUnits ℂ p.1 * p.2.val := rfl

private def triangularLeftCorrection (b : B) (d : D) : U :=
  ((complexTriangularCoordinates n).symm (b * complexTriangularCoordinates n (d, 1))).2

private theorem triangularCoordinates_left_mul (b : B) (p : D × U) :
    (complexTriangularCoordinates n).symm (b * complexTriangularCoordinates n p) =
      (triangularDiagonal n ℂ b * p.1, triangularLeftCorrection n b p.1 * p.2) := by
  have h (d : D) (u : U) : triangularDiagonal n ℂ (b * complexTriangularCoordinates n (d, u)) =
      triangularDiagonal n ℂ b * d := by
    change triangularDiagonal n ℂ (b * (diagonalInB n d * unipotentInB n u)) = _
    simp
  obtain ⟨d, u⟩ := p
  apply Prod.ext (h d u)
  apply Subtype.ext
  have h1 := h d 1
  change ((diagonalInB n (triangularDiagonal n ℂ (b * complexTriangularCoordinates n (d, u))))⁻¹ *
      (b * complexTriangularCoordinates n (d, u)) : B).val =
    ((diagonalInB n (triangularDiagonal n ℂ (b * complexTriangularCoordinates n (d, 1))))⁻¹ *
      (b * complexTriangularCoordinates n (d, 1)) : B).val * u.val
  rw [h d u, h1]
  change _ = (_ : B).val * (unipotentInB n u).val
  rw [← Subgroup.coe_mul]
  congr 1
  change _ * (b * (diagonalInB n d * unipotentInB n u)) =
    (_ * (b * (diagonalInB n d * unipotentInB n 1))) * unipotentInB n u
  rw [map_one, mul_one]
  group

local instance triangularMatrixSecondCountable : SecondCountableTopology M :=
  inferInstanceAs (SecondCountableTopology (I → I → ℂ))
local instance triangularGLSecondCountable : SecondCountableTopology G :=
  (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).isInducing.secondCountableTopology
local instance triangularUnitsSecondCountable : SecondCountableTopology (ℂˣ) :=
  (show IsEmbedding (Units.val : ℂˣ → ℂ) from Units.isEmbedding_val₀).isInducing.secondCountableTopology
local instance triangularGLMeasurable : MeasurableSpace G := borel _
local instance triangularGLBorel : BorelSpace G := ⟨rfl⟩
local instance triangularUnitsMeasurable : MeasurableSpace (ℂˣ) := borel _
local instance triangularUnitsBorel : BorelSpace (ℂˣ) := ⟨rfl⟩

private theorem complexTriangularCoordinates_map_isHaar
    (μD : Measure D) [μD.IsHaarMeasure] [SFinite μD]
    (μU : Measure U) [μU.IsHaarMeasure] [SFinite μU] :
    ((μD.prod μU).map (complexTriangularCoordinates n)).IsHaarMeasure := by
  let e := complexTriangularCoordinates n
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
  have ht := (measurePreserving_mul_left μD (triangularDiagonal n ℂ b)).skew_product
    hm (Filter.Eventually.of_forall fun d =>
      (measurePreserving_mul_left μU (triangularLeftCorrection n b d)).map_eq)
  have hmul : Measurable (fun c : B => b * c) := (continuous_const.mul continuous_id).measurable
  have hfun : (fun c : B => b * c) ∘ e =
      e ∘ (fun p : D × U => (triangularDiagonal n ℂ b * p.1,
        triangularLeftCorrection n b p.1 * p.2)) := by
    funext p
    exact (e.apply_symm_apply (b * e p)).symm.trans
      (congrArg e (triangularCoordinates_left_mul n b p))
  change μB.map (fun c : B => b * c) = μB
  dsimp only [μB]
  rw [Measure.map_map hmul he, hfun, ← Measure.map_map he ht.measurable, ht.map_eq]

/-- Haar measure agrees, up to one finite positive constant, with the product
of left Haar measures in diagonal, upper-unipotent and unitary coordinates. -/
theorem exists_complexMatrixHaar_eq_triangular (μ : Measure M) [μ.IsAddHaarMeasure]
    (μD : Measure D) [μD.IsHaarMeasure] [SFinite μD]
    (μU : Measure U) [μU.IsHaarMeasure] [SFinite μU]
    (μK : Measure Kc) [μK.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ complexMatrixHaar n μ =
      c • (((μD.prod μU).prod μK).map
        (fun p : (D × U) × Kc => diagonalMatrixUnits ℂ p.1.1 * p.1.2.val * p.2.val)) := by
  let : LocallyCompactSpace M := inferInstanceAs (LocallyCompactSpace (I → I → ℂ))
  let : LocallyCompactSpace G :=
    (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).locallyCompactSpace
  let : (complexMatrixHaar n μ).IsHaarMeasure := complexMatrixHaar_isHaar n μ
  let e := complexTriangularCoordinates n
  let μB := (μD.prod μU).map e
  let : μB.IsHaarMeasure := complexTriangularCoordinates_map_isHaar n μD μU
  have hBK (g : G) : ∃ b ∈ B, ∃ k ∈ Kc, g = b * k := by
    obtain ⟨d, u, k, hk, rfl⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
    exact ⟨_, (e (d, u)).property, k, hk, rfl⟩
  obtain ⟨c, hc, he⟩ := CompactFactorization.exists_pos_eq_smul_map_mul_prod
    (complexMatrixHaar n μ) B isClosed_upperTriangular Kc (ComplexDuality.isCompact_unitaryCompact n)
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

end Langlands.GodementJacquet
