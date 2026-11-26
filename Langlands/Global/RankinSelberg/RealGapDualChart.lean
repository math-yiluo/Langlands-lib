import Langlands.Global.RankinSelberg.RealGapUnitDeterminant
import Langlands.Global.RankinSelberg.RealGapWeylRestriction
import Langlands.Global.RankinSelberg.RealTriangularInversion
import Langlands.Representation.Archimedean.MaximalParabolicIntegration
import Langlands.Representation.GodementJacquet.TwoBlockDualParabolicIntegral
import Langlands.Representation.RankinSelberg.UnequalRankBlockCoordinates
import Langlands.Group.GL.LowerBlockQuotientCoordinates

/-! # The dual chart obtained by inverse transpose and tail reversal -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapDualChart

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.MaximalParabolicIntegration (det_upperUnipotent)
open Langlands.GeneralLinear (rankInclusion blockSum inverseTranspose inverseTransposeContinuous
  lowerBlockPair weylLong weylLong_inv)
open Langlands.GodementJacquet (transposeMeasurableEquiv measurePreserving_transpose_rectangularMeasure
  realHaar_measurePreserving_inverseTranspose)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.RankinSelberg (rectangularMeasure)
open RealGapTriangularChart (Outer)
open RealGapUnitDeterminant
open RealGapUpperTail (packedTail packedTail_mul laterRectangle)
open RealGapWeylRestriction (tailWeyl)
open RealJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local instance gapGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
local instance gapGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  Units.isOpenEmbedding_val.locallyCompactSpace

variable (k q : ℕ)
local notation "Size" => k + q + 1
local notation "TailSize" => q + 1
local notation "Compact" => unitaryCompact ℝ Size
local notation "N" => Langlands.GeneralLinear.upperUnipotent TailSize ℝ
local notation "R" => Matrix (Fin k) (Fin q) ℝ
local notation "U" => Matrix (Fin q) (Fin k) ℝ
local notation "FullLower" => Matrix (Fin TailSize) (Fin k) ℝ
local notation "ι" => inverseTranspose Size ℝ
local notation "ι₁" => inverseTranspose k ℝ
local notation "w" => tailWeyl k TailSize
local notation "e" => (finSumFinEquiv : Fin k ⊕ Fin TailSize ≃ Fin Size)

local instance gapTailMeasurable : MeasurableSpace N := borel _
local instance gapTailBorel : BorelSpace N := ⟨rfl⟩

/-- Transpose the later rectangle and reverse its rows. -/
def reverseTranspose (X : R) : U := fun i j => X j i.rev

/-- The rectangle transposition and reversal identify the two product measures. -/
theorem measurePreserving_reverseTranspose (μ : AdditiveHaarMeasure ℝ) :
    MeasurePreserving (reverseTranspose k q) (rectangularMeasure μ k q) (rectangularMeasure μ q k) := by
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let ν := Langlands.HarmonicAnalysis.rowMeasure μ k
  have hT := measurePreserving_transpose_rectangularMeasure μ k q
  have hR := measurePreserving_piCongrLeft (fun _ : Fin q => ν) (Fin.revPerm : Equiv.Perm (Fin q))
  convert hR.comp hT using 1 <;> try rfl
  funext X i j
  obtain ⟨i, rfl⟩ := (Fin.revPerm : Equiv.Perm (Fin q)).surjective i
  change X j i.rev.rev = MeasurableEquiv.piCongrLeft (fun _ => Fin k → ℝ) Fin.revPerm
    (transposeMeasurableEquiv k q X) (Fin.revPerm i) j
  rw [Fin.rev_rev, MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

/-- Extend the lower rectangle by one zero row. -/
def extendLower (X : U) : FullLower := Fin.lastCases 0 X

@[simp] theorem extendLower_castSucc (X : U) (i : Fin q) : extendLower k q X i.castSucc = X i := by
  simp [extendLower]

@[simp] theorem extendLower_last (X : U) : extendLower k q X (Fin.last q) = 0 := by
  simp [extendLower]

/-- Lower unipotent addition in the full complementary rectangle. -/
def lowerShear (X : FullLower) : G Size := lowerBlockPair (a := k) (d := TailSize) 1 X 1

theorem lowerShear_mul (X Y : FullLower) : lowerShear k q X * lowerShear k q Y = lowerShear k q (X + Y) := by
  apply Units.ext
  change (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 X (1 : Matrix (Fin TailSize) (Fin TailSize) ℝ)).submatrix (e).symm (e).symm *
      (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 Y (1 : Matrix (Fin TailSize) (Fin TailSize) ℝ)).submatrix (e).symm (e).symm = _
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rfl

theorem lowerShear_zero : lowerShear k q 0 = 1 := by
  apply Units.ext
  change (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 0 (1 : Matrix (Fin TailSize) (Fin TailSize) ℝ)).submatrix (e).symm (e).symm = _
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv (e).symm

theorem lowerShear_inv (X : FullLower) : (lowerShear k q X)⁻¹ = lowerShear k q (-X) := by
  rw [inv_eq_iff_mul_eq_one, lowerShear_mul, add_neg_cancel, lowerShear_zero]

theorem determinant_lowerShear (X : FullLower) : Langlands.GeneralLinear.determinant (lowerShear k q X) = 1 := by
  apply Units.ext
  change (Matrix.reindex (e) (e) (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 X
    (1 : Matrix (Fin TailSize) (Fin TailSize) ℝ))).det = 1
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_one, mul_one]

/-- Retain the upper unipotent tail and first rectangular column in the normalized chart. -/
def retainedTail (p : Outer k q) (Z : N) : G Size :=
  unitRetained k q p * (packedTail k q 0 Z).val

theorem normalizedAbs_retainedTail (hk : 0 < k) (p : Outer k q) (Z : N) :
    ArchimedeanLocal.realNormalizedAbs (retainedTail k q p Z).val.det = 1 := by
  unfold retainedTail
  rw [Units.val_mul, Matrix.det_mul, det_upperUnipotent, mul_one, normalizedAbs_unitRetained k q hk]

private theorem unitDeterminantChart_split (p : Outer k q) (X : R) (Z : N) :
    unitDeterminantChart k q (p, X, Z) =
      retainedTail k q p Z * (packedTail k q (laterRectangle k q X) 1).val * rankInclusion TailSize p.1.1.1 := by
  have h := congrArg Subtype.val (packedTail_mul k q 0 (laterRectangle k q X) Z (1 : N))
  simp only [Subgroup.coe_mul, Matrix.zero_mul, add_zero, mul_one] at h
  change unitRetained k q p * (packedTail k q (laterRectangle k q X) Z).val * rankInclusion TailSize p.1.1.1 =
    (unitRetained k q p * (packedTail k q 0 Z).val) * (packedTail k q (laterRectangle k q X) 1).val *
      rankInclusion TailSize p.1.1.1
  rw [mul_assoc (unitRetained k q p) (packedTail k q 0 Z).val, h]

theorem inverseTranspose_rankInclusion (h : G k) :
    ι (rankInclusion TailSize h) = rankInclusion TailSize (ι₁ h) := by
  apply Units.ext
  simp only [Langlands.GeneralLinear.inverseTranspose_coe, ← map_inv (rankInclusion TailSize)]
  change ((Matrix.fromBlocks h⁻¹.val 0 0 (1 : Matrix (Fin TailSize) (Fin TailSize) ℝ)).submatrix
    (e).symm (e).symm).transpose = _
  rw [Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_zero,
    Matrix.transpose_one]
  rfl

theorem tailWeyl_commutes_rankInclusion (h : G k) :
    w * rankInclusion TailSize h = rankInclusion TailSize h * w := by
  unfold tailWeyl
  change blockSum (1, weylLong TailSize ℝ) * blockSum (h, 1) =
    blockSum (h, 1) * blockSum (1, weylLong TailSize ℝ)
  simp only [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

private theorem laterRectangle_invTranspose (X : R) :
    ι (packedTail k q (laterRectangle k q X) 1).val = lowerShear k q (-(laterRectangle k q X).transpose) := by
  apply Units.ext
  change ((Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) (-(laterRectangle k q X * 1)) 0
      (1 : Matrix (Fin TailSize) (Fin TailSize) ℝ)).submatrix (e).symm (e).symm).transpose = _
  rw [Matrix.mul_one, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.transpose_one, Matrix.transpose_one, Matrix.transpose_neg]
  rfl

private theorem reversed_laterRectangle (X : R) :
    (weylLong TailSize ℝ).val * (laterRectangle k q X).transpose = extendLower k q (reverseTranspose k q X) := by
  ext i j
  rw [Langlands.RankinSelberg.weylLong_mul_apply]
  refine Fin.lastCases ?_ (fun i₀ => ?_) i
  · simp only [Fin.rev_last, Matrix.transpose_apply, laterRectangle, Fin.cons_zero,
      extendLower_last, Pi.zero_apply]
  · simp only [Fin.rev_castSucc, Matrix.transpose_apply, laterRectangle, Fin.cons_succ,
      extendLower_castSucc, reverseTranspose]

private theorem conjugate_inverseTranspose (X : R) :
    ι (packedTail k q (laterRectangle k q X) 1).val * w =
      w * lowerShear k q (-extendLower k q (reverseTranspose k q X)) := by
  rw [laterRectangle_invTranspose]
  apply Units.ext
  change (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 (-(laterRectangle k q X).transpose)
      (1 : Matrix (Fin TailSize) (Fin TailSize) ℝ)).submatrix (e).symm (e).symm *
      (Matrix.fromBlocks 1 0 0 (weylLong TailSize ℝ).val).submatrix (e).symm (e).symm =
    (Matrix.fromBlocks 1 0 0 (weylLong TailSize ℝ).val).submatrix (e).symm (e).symm *
      (Matrix.fromBlocks 1 0 (-extendLower k q (reverseTranspose k q X)) 1).submatrix (e).symm (e).symm
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_neg, neg_zero]
  rw [← reversed_laterRectangle, ← Matrix.mul_assoc, ← Units.val_mul,
    Langlands.GeneralLinear.weylLong_mul_self, Units.val_one, Matrix.one_mul]

/-- Inverse transpose followed by tail reversal moves the retained matrix to the dual chart. -/
def dualRetained (p : Outer k q) (Z : N) : G Size := ι (retainedTail k q p Z) * w

/-- The dual chart places the negated lower rectangle before the inverse transpose of the leading factor. -/
def dualChart (p : Outer k q × (U × N)) : G Size :=
  dualRetained k q p.1 p.2.2 * lowerShear k q (-extendLower k q p.2.1) * rankInclusion TailSize (ι₁ p.1.1.1.1)

private theorem chart_change (p : Outer k q × (R × N)) :
    ι (unitDeterminantChart k q p) * w = dualChart k q (p.1, reverseTranspose k q p.2.1, p.2.2) := by
  rcases p with ⟨p,X,Z⟩
  rw [unitDeterminantChart_split, map_mul, map_mul, inverseTranspose_rankInclusion, mul_assoc _ _ w,
    ← tailWeyl_commutes_rankInclusion, ← mul_assoc _ w _, mul_assoc (ι (retainedTail k q p Z)),
    conjugate_inverseTranspose]
  simp only [dualChart, dualRetained, mul_assoc]

/-- The dual chart is measurable in the same Borel structures as the Haar formula. -/
theorem measurable_dualChart : Measurable (dualChart k q) := by
  let : SecondCountableTopology Compact := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology N := (Langlands.GeneralLinear.upperEntryCoordinates (K := ℝ) TailSize).secondCountableTopology
  let D := fun g : G Size => ι g * w
  let E := Prod.map (id : Outer k q → Outer k q) (Prod.map (reverseTranspose k q) (id : N → N))
  have hC : D ∘ unitDeterminantChart k q = dualChart k q ∘ E := funext (chart_change k q)
  have hD : Measurable D := ((inverseTransposeContinuous Size ℝ).continuous.mul continuous_const).measurable
  have hm : Measurable (unitDeterminantChart k q) := (continuous_unitDeterminantChart k q).measurable
  let V (p : Outer k q × (U × N)) : Outer k q × (R × N) := (p.1, (fun i j => p.2.1 j.rev i), p.2.2)
  have hRect : Measurable (fun p : Outer k q × (U × N) => (fun i j => p.2.1 j.rev i : R)) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply.comp (measurable_fst.comp measurable_snd)
  have hV : Measurable V := measurable_fst.prodMk (hRect.prodMk (measurable_snd.comp measurable_snd))
  have hInv : E ∘ V = id := by
    funext p
    rcases p with ⟨p, X, Z⟩
    change (p, (fun i j => X i.rev.rev j : U), Z) = (p, X, Z)
    simp only [Fin.rev_rev]
  have hh := (hD.comp hm).comp hV
  rw [hC, Function.comp_assoc, hInv, Function.comp_id] at hh
  exact hh

/-- The same Haar normalization constant works for the ordinary and inverse-transpose charts. -/
def RealGapDualChartStatement : Prop :=
  ∀ (_hk : 0 < k) (μ : AdditiveHaarMeasure ℝ) (η : Measure (G Size)) (η₁ : Measure (G k))
    (κ : Measure Compact), η.IsHaarMeasure → η₁.IsHaarMeasure → κ.IsHaarMeasure → κ.IsInvInvariant →
    ∃ c : ℝ≥0, 0 < c ∧
      η = c • ((unitOuterMeasure k q μ η₁ κ).prod
        ((rectangularMeasure μ k q).prod (entryHaar μ TailSize))).map (unitDeterminantChart k q) ∧
      η = c • ((unitOuterMeasure k q μ η₁ κ).prod
        ((rectangularMeasure μ q k).prod (entryHaar μ TailSize))).map (dualChart k q)

set_option maxHeartbeats 1000000 in
theorem realGapDualChart : RealGapDualChartStatement k q := by
  intro hk μ Haar η₁ κ hHaar₀ hη₁ hκ hκinv
  obtain ⟨c, hc, hHaar⟩ := realGapUnitDeterminant k q hk μ Haar η₁ κ hHaar₀ hη₁ hκ hκinv
  let : Haar.IsHaarMeasure := hHaar₀
  let : η₁.IsHaarMeasure := hη₁
  let : Haar.IsMulRightInvariant := (RealGodement.realMatrixHaar_symmetries Haar).1
  let η := entryHaar μ TailSize
  let σ := unitOuterMeasure k q μ η₁ κ
  let τ := (rectangularMeasure μ k q).prod η
  let τd := (rectangularMeasure μ q k).prod η
  let : κ.IsHaarMeasure := hκ
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : SigmaFinite η := entryHaar_sigmaFinite μ _
  let : SigmaFinite (RealGapTriangularChart.outerMeasure k q μ η₁ κ) := by
    unfold RealGapTriangularChart.outerMeasure
    infer_instance
  let : SigmaFinite σ := SigmaFinite.withDensity _
  let : SecondCountableTopology Compact := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology N := (Langlands.GeneralLinear.upperEntryCoordinates (K := ℝ) TailSize).secondCountableTopology
  let D := fun g : G Size => ι g * w
  let E := Prod.map (id : Outer k q → Outer k q) (Prod.map (reverseTranspose k q) (id : N → N))
  have hD : MeasurePreserving D Haar Haar := (measurePreserving_mul_right Haar w).comp
    (realHaar_measurePreserving_inverseTranspose Size Haar)
  have hE : MeasurePreserving E (σ.prod τ) (σ.prod τd) :=
    (MeasurePreserving.id _).prod ((measurePreserving_reverseTranspose k q μ).prod (MeasurePreserving.id _))
  have hC : D ∘ unitDeterminantChart k q = dualChart k q ∘ E := funext (chart_change k q)
  have hm : Measurable (unitDeterminantChart k q) := (continuous_unitDeterminantChart k q).measurable
  refine ⟨c, hc, hHaar, ?_⟩
  change Haar = c • (σ.prod τ).map (unitDeterminantChart k q) at hHaar
  change Haar = c • (σ.prod τd).map (dualChart k q)
  calc
    Haar = Haar.map D := hD.map_eq.symm
    _ = c • (σ.prod τd).map (dualChart k q) := by
      rw [hHaar, Measure.map_smul _ hD.measurable.aemeasurable, map_map hD.measurable hm,
        hC, ← map_map (measurable_dualChart k q) hE.measurable, hE.map_eq]

end Langlands.Global.RankinSelbergGlobal.RealGapDualChart
