import Langlands.Global.RankinSelberg.RealParabolicHaar
import Langlands.Global.RankinSelberg.RealGodementHaar
import Langlands.Group.GL.TwoBlockShape
import Langlands.Group.GL.BlockUnipotentCoordinates
import Langlands.Group.GL.LeviCentralQuotientMeasure
import Langlands.Representation.RankinSelberg.Measures

/-! # Rectangular two-block coordinates for real general linear Haar measure -/

noncomputable section

open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Classical Matrix.Norms.Operator NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealTwoBlockHaar

open Langlands.ProductLeviChamber (twoBlock)
open Langlands.Archimedean (unitaryCompact)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.RankinSelberg (rectangularMeasure rectangularMeasure_isAddHaar)
open RealParabolicHaar (leviRadicalOrthogonal orthogonalRadicalLevi realParabolicHaar)
open RealGodement (realMatrixHaar_symmetries)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "K" => fun n => unitaryCompact ℝ n
local notation "Rect" => fun n k => Matrix (Fin k) (Fin (n - k)) ℝ

local instance twoBlockHaarGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance twoBlockHaarGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance twoBlockHaarGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
local instance twoBlockHaarGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  Units.isOpenEmbedding_val.locallyCompactSpace
local instance twoBlockHaarGLMetrizable (n : ℕ) : MetrizableSpace (G n) :=
  Units.isOpenEmbedding_val.isEmbedding.metrizableSpace

variable {n k : ℕ} (hk : 0 < k) (hkn : k < n)

local notation "B" => twoBlock n k hk hkn
local notation "U" => Langlands.GeneralLinear.BlockShape.unipotentRadical (twoBlock n k hk hkn) ℝ
local notation "L" => Langlands.GeneralLinear.BlockShape.Levi (twoBlock n k hk hkn) ℝ

private def rectangleIndex : (B).UpperPair := ⟨((0 : Fin 2), (1 : Fin 2)), by
  change (0 : ℕ) < 1
  decide⟩

private instance rectangleIndexUnique : Unique (B).UpperPair where
  default := rectangleIndex hk hkn
  uniq p := by
    apply Subtype.ext
    have hi : p.val.1.val < 2 := p.val.1.isLt
    have hj : p.val.2.val < 2 := p.val.2.isLt
    have hp : p.val.1.val < p.val.2.val := p.2
    exact Prod.ext (Fin.ext (show p.val.1.val = 0 by omega)) (Fin.ext (show p.val.2.val = 1 by omega))

/-- The only strictly upper block of the two-block unipotent radical. -/
def rectangleCoordinates : U ≃ₜ Rect n k :=
  ((B).radicalCoordinatesHomeomorph ℝ).trans
    (Homeomorph.piUnique fun p : (B).UpperPair => Matrix (Fin ((B).size p.val.1)) (Fin ((B).size p.val.2)) ℝ)

theorem rectangleCoordinates_mul (u v : U) :
    rectangleCoordinates hk hkn (u * v) = rectangleCoordinates hk hkn u + rectangleCoordinates hk hkn v := by
  let : IsEmpty {j : Fin (B).length //
      (show Fin (B).length from (0 : Fin 2)) < j ∧ j < (show Fin (B).length from (1 : Fin 2))} := ⟨fun j => by
    have h0 : 0 < j.val.val := j.2.1
    have h1 : j.val.val < 1 := j.2.2
    omega⟩
  have h := (B).radicalCoordinates_mul ℝ u v (show (0 : Fin 2) < 1 by decide)
  rw [Finset.sum_of_isEmpty, add_zero] at h
  exact h

theorem rectangleCoordinates_inv (u : U) :
    rectangleCoordinates hk hkn u⁻¹ = -rectangleCoordinates hk hkn u := by
  have h := rectangleCoordinates_mul hk hkn u⁻¹ u
  rw [inv_mul_cancel] at h
  have hOne : rectangleCoordinates hk hkn (1 : U) = 0 := by
    change (B).radicalCoordinates ℝ (1 : U) (rectangleIndex hk hkn) = 0
    rw [(B).radicalCoordinates_one]
    rfl
  exact eq_neg_of_add_eq_zero_left (h.symm.trans hOne)

/-- The actual upper unipotent matrix with just the specified off-diagonal block. -/
def upperRectangle (X : Rect n k) : G n := ((rectangleCoordinates hk hkn).symm X).val.val

/-- The two diagonal blocks identify the Levi with the product of the actual general
linear groups of the two sizes. -/
def leviBlocks : L ≃ₜ* G k × G (n - k) :=
  let e := Homeomorph.piFinTwo fun i : Fin 2 => G ((B).size i)
  { toMulEquiv := { toEquiv := e.toEquiv, map_mul' := fun _ _ => rfl }
    continuous_toFun := e.continuous
    continuous_invFun := e.symm.continuous }

/-- Insert two actual general linear matrices in the two diagonal blocks. -/
def diagonalBlocks (g₁ : G k) (g₂ : G (n - k)) : G n :=
  (B).leviEmbedding ℝ ((leviBlocks hk hkn).symm (g₁, g₂))

private theorem rectangleHaar_isHaar (ρ : Measure (Rect n k)) [ρ.IsAddHaarMeasure] :
    (ρ.map (rectangleCoordinates hk hkn).symm).IsHaarMeasure := by
  let e := rectangleCoordinates hk hkn
  let ν := ρ.map e.symm
  let : IsFiniteMeasureOnCompacts ν := IsFiniteMeasureOnCompacts.map ρ e.symm
  let : IsOpenPosMeasure ν := e.symm.continuous.isOpenPosMeasure_map e.symm.surjective
  refine { map_mul_left_eq_self := fun u => ?_ }
  have he : (u * ·) ∘ e.symm = e.symm ∘ (e u + ·) := by
    funext X
    apply e.injective
    simp only [Function.comp_apply, e.apply_symm_apply]
    rw [rectangleCoordinates_mul hk hkn u (e.symm X)]
    exact congrArg (e u + ·) (e.apply_symm_apply X)
  change (ρ.map e.symm).map (u * ·) = ρ.map e.symm
  rw [Measure.map_map (measurable_const_mul _) e.symm.measurable, he,
    ← Measure.map_map e.symm.measurable (measurable_const_add _), map_add_left_eq_self]

private theorem rectangleHaar_isInvInvariant (ρ : Measure (Rect n k)) [ρ.IsNegInvariant] :
    (ρ.map (rectangleCoordinates hk hkn).symm).IsInvInvariant := by
  let e := rectangleCoordinates hk hkn
  constructor
  have he : Inv.inv ∘ e.symm = e.symm ∘ Neg.neg := by
    funext X
    apply e.injective
    simp only [Function.comp_apply, e.apply_symm_apply]
    rw [rectangleCoordinates_inv hk hkn (e.symm X)]
    exact congrArg Neg.neg (e.apply_symm_apply X)
  change (ρ.map e.symm).map (Inv.inv : U → U) = ρ.map e.symm
  rw [Measure.map_map measurable_inv e.symm.measurable, he,
    ← Measure.map_map e.symm.measurable measurable_neg, map_neg_eq_self]

private theorem leviHaar_isInvInvariant (μ₁ : Measure (G k)) (μ₂ : Measure (G (n - k)))
    [μ₁.IsInvInvariant] [μ₂.IsInvInvariant] [SFinite μ₁] [SFinite μ₂] :
    ((μ₁.prod μ₂).map (leviBlocks hk hkn).symm).IsInvInvariant := by
  let e := leviBlocks hk hkn
  constructor
  have he : Inv.inv ∘ e.symm = e.symm ∘ (Inv.inv : G k × G (n - k) → _) := by
    funext x
    exact (map_inv e.symm x).symm
  change ((μ₁.prod μ₂).map e.symm).map (Inv.inv : L → L) = (μ₁.prod μ₂).map e.symm
  have hem : Measurable (e.symm : G k × G (n - k) → L) := e.symm.continuous.measurable
  rw [Measure.map_map measurable_inv hem, he, ← Measure.map_map hem measurable_inv]
  exact congrArg (Measure.map e.symm) ((measurePreserving_inv μ₁).prod (measurePreserving_inv μ₂)).map_eq

/-- Haar measure in the two-block coordinates, with a supplied real additive scalar
measure for the rectangular factor and arbitrary Haar measures on the general linear groups. -/
def RealTwoBlockHaarStatement : Prop :=
  ∀ (n k : ℕ) (hk : 0 < k) (hkn : k < n) (ν : AdditiveHaarMeasure ℝ) (μ : Measure (G n))
    (μ₁ : Measure (G k)) (μ₂ : Measure (G (n - k))) (κ : Measure (K n)),
    μ.IsHaarMeasure → μ₁.IsHaarMeasure → μ₂.IsHaarMeasure →
    κ.IsHaarMeasure → κ.IsInvInvariant → ∃ c : ℝ≥0, 0 < c ∧
    μ = c • Measure.map
      (fun p : ((G k × G (n - k)) × Rect n k) × K n =>
        p.2.val * upperRectangle hk hkn p.1.2 * diagonalBlocks hk hkn p.1.1.1 p.1.1.2)
      (((μ₁.prod μ₂).prod (rectangularMeasure ν k (n - k))).prod κ)

set_option maxHeartbeats 1200000 in
theorem realTwoBlockHaar : RealTwoBlockHaarStatement := by
  intro n k hk hkn ν μ μ₁ μ₂ κ hμ hμ₁ hμ₂ hκ hκinv
  let S := twoBlock n k hk hkn
  let : μ.IsHaarMeasure := hμ
  let : μ₁.IsHaarMeasure := hμ₁
  let : μ₂.IsHaarMeasure := hμ₂
  let : κ.IsHaarMeasure := hκ
  let : κ.IsInvInvariant := hκinv
  let ρ := rectangularMeasure ν k (n - k)
  let : ν.measure.IsAddHaarMeasure := ν.isAddHaar
  let : ρ.IsAddHaarMeasure := rectangularMeasure_isAddHaar ν k (n - k)
  let eL := leviBlocks hk hkn
  let eU := rectangleCoordinates hk hkn
  let μL := (μ₁.prod μ₂).map eL.symm
  let μU := ρ.map eU.symm
  let : SigmaFinite ρ := inferInstance
  let : SigmaFinite μ₁ := inferInstance
  let : SigmaFinite μ₂ := inferInstance
  let : SigmaFinite κ := inferInstance
  let : μL.IsHaarMeasure := eL.symm.isHaarMeasure_map (μ₁.prod μ₂)
  let : μU.IsHaarMeasure := rectangleHaar_isHaar hk hkn ρ
  let : PseudoMetrizableSpace (Rect n k) := inferInstanceAs
    (PseudoMetrizableSpace (Fin k → Fin (n - k) → ℝ))
  let : SigmaCompactSpace (Rect n k) := inferInstanceAs
    (SigmaCompactSpace (Fin k → Fin (n - k) → ℝ))
  let : ρ.Regular := inferInstance
  let : μ.IsInvInvariant := (realMatrixHaar_symmetries μ).2
  let : μ₁.IsInvInvariant := (realMatrixHaar_symmetries μ₁).2
  let : μ₂.IsInvInvariant := (realMatrixHaar_symmetries μ₂).2
  let : μL.IsInvInvariant := leviHaar_isInvInvariant hk hkn μ₁ μ₂
  let : μU.IsInvInvariant := rectangleHaar_isInvInvariant hk hkn ρ
  obtain ⟨c, hc, _, hRight⟩ := realParabolicHaar n S μ μL μU κ
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)
  refine ⟨c, hc, ?_⟩
  rw [hRight (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)]
  have hLevi : Measurable (eL.symm : G k × G (n - k) → S.Levi ℝ) :=
    eL.symm.continuous.measurable
  have hRadical : Measurable (eU.symm : Rect n k → S.unipotentRadical ℝ) := eU.symm.measurable
  have hProd : (μL.prod μU).prod κ = Measure.map (Prod.map (Prod.map eL.symm eU.symm) id)
      (((μ₁.prod μ₂).prod ρ).prod κ) := by
    rw [← Measure.map_prod_map _ _ (hLevi.prodMap hRadical) measurable_id,
      ← Measure.map_prod_map _ _ hLevi hRadical, Measure.map_id]
  let P := (S.Levi ℝ × S.unipotentRadical ℝ) × K n
  have hK : Measurable (fun p : P => p.2.val) := measurable_subtype_coe.comp measurable_snd
  have hU : Measurable (fun p : P => p.1.2.val.val) :=
    (measurable_subtype_coe.comp measurable_subtype_coe).comp (measurable_snd.comp measurable_fst)
  have hL : Measurable (fun p : P => S.leviEmbedding ℝ p.1.1) :=
    (S.leviEmbeddingContinuous ℝ).continuous.measurable.comp (measurable_fst.comp measurable_fst)
  have hM : Measurable (orthogonalRadicalLevi S) := (hK.mul hU).mul hL
  rw [hProd, Measure.map_map hM ((hLevi.prodMap hRadical).prodMap measurable_id)]
  rfl

end Langlands.Global.RankinSelbergGlobal.RealTwoBlockHaar
