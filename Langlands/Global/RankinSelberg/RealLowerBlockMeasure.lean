import Langlands.Global.RankinSelberg.ArchimedeanRealPairIdentity
import Langlands.Group.GL.LowerTriangularBlockCoordinates
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLDensity
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Mathlib.MeasureTheory.Group.Prod

/-! # Real determinant-weighted lower block measures -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Matrix
open scoped NNReal ENNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

namespace Langlands.Global.RankinSelbergGlobal.RealLowerBlockMeasure

open Langlands.GeneralLinear Langlands.QuotientIntegration Langlands.HarmonicAnalysis
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure unipotent_det)
open Langlands.RankinSelberg.GLDeterminantDensity (map_withDensity_equiv)
open ArchimedeanLocal
open ArchimedeanRealPairIdentity (quotientDetAbs quotientDetAbs_pos continuous_quotientDetAbs
  sigmaFinite_measure sigmaFinite_rect sigmaFinite_haar)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (r : ℕ) : MeasurableSpace (LeftUnipotentQuotient r ℝ) := borel _
private local instance (r : ℕ) : BorelSpace (LeftUnipotentQuotient r ℝ) := ⟨rfl⟩
private local instance (d : ℕ) : MeasurableSpace (lowerTriangularSubgroup d ℝ) := borel _
private local instance (d : ℕ) : BorelSpace (lowerTriangularSubgroup d ℝ) := ⟨rfl⟩
private local instance (d : ℕ) : SecondCountableTopology (Langlands.GeneralLinear d ℝ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
private local instance (d : ℕ) : SecondCountableTopology (lowerTriangularSubgroup d ℝ) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

variable {r d : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "N" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "Q" => LeftUnipotentQuotient r ℝ
local notation "X" => Matrix (Fin d) (Fin (r + 1)) ℝ
local notation "B" => lowerTriangularSubgroup d ℝ

private theorem quotientDetAbs_mk (g : G) : quotientDetAbs (Quotient.mk _ g : Q) = |g.val.det| := by
  let f : G → ℝ := fun x => |x.val.det|
  have hf (u : N) (x : G) : f (u.val * x) = f x := by
    simp only [f, Units.val_mul, Matrix.det_mul, unipotent_det, one_mul]
  exact RealEqualConvergence.out_eq_descend f hf (Quotient.mk _ g)

private theorem quotientDetAbs_right (g : G) (q : Q) :
    quotientDetAbs (rightTranslate N g q) = quotientDetAbs q * |g.val.det| := by
  induction q using Quotient.inductionOn with
  | h x => rw [rightTranslate_mk, quotientDetAbs_mk, quotientDetAbs_mk, Units.val_mul, Matrix.det_mul, abs_mul]

/-- The quotient density `|det g|⁻ᵈ` for a trailing block of size `d`. -/
def lowerBlockDensity (d : ℕ) (q : Q) : ℝ≥0∞ := ↑(((quotientDetAbs q).toNNReal ^ d)⁻¹ : ℝ≥0)

private theorem measurable_lowerBlockDensity (d : ℕ) : Measurable (lowerBlockDensity (r := r) d) := by
  unfold lowerBlockDensity
  have h : Continuous (fun q : Q => (quotientDetAbs q).toNNReal) :=
    continuous_real_toNNReal.comp continuous_quotientDetAbs
  exact Measurable.coe_nnreal_ennreal ((h.pow d).measurable.inv)

/-- The lower-block product of the weighted smaller quotient, additive rectangular
measure and the supplied measure of the trailing triangular group. -/
def lowerBlockProduct (D : RealQuotientMeasureData r) (ν : AdditiveHaarMeasure ℝ) (ρ : Measure B) :
    Measure (LowerBlockQuotientParameters (r + 1) d ℝ) :=
  (D.measure.withDensity (lowerBlockDensity d)).prod ((rectangularMeasure ν d (r + 1)).prod ρ)

/-- The lower-block right multiplication in the actual quotient coordinates. -/
def lowerBlockRight (g : G) (y : X) (h : B) (z : LowerBlockQuotientParameters (r + 1) d ℝ) :
    LowerBlockQuotientParameters (r + 1) d ℝ :=
  (rightTranslate N g z.1, z.2.1 * g.val + z.2.2.val.val * y, z.2.2 * h)

private theorem map_weightedQuotient (D : RealQuotientMeasureData r) (g : G) :
    (D.measure.withDensity (lowerBlockDensity d)).map (rightTranslate N g) =
      (‖g.val.det‖₊ ^ d) • D.measure.withDensity (lowerBlockDensity d) := by
  let := D.unipotentHaar_rightInvariant
  let e := (rightTranslate N g).toMeasurableEquiv
  have he : D.measure.map e = D.measure := (D.compatible.right_invariant g).map_eq
  have hen (q : Q) : lowerBlockDensity d (e.symm q) =
      (↑(‖g.val.det‖₊ ^ d) : ℝ≥0∞) * lowerBlockDensity d q := by
    have hg : |(g⁻¹).val.det| = |g.val.det|⁻¹ := by
      change |((Matrix.GeneralLinearGroup.det g⁻¹ : ℝˣ) : ℝ)| = _
      rw [map_inv, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply, abs_inv]
    change lowerBlockDensity d (rightTranslate N g⁻¹ q) = _
    rw [lowerBlockDensity, quotientDetAbs_right, hg,
      Real.toNNReal_mul (quotientDetAbs_pos q).le, mul_pow, mul_inv, Real.toNNReal_inv,
      inv_pow, inv_inv]
    have hn : |g.val.det|.toNNReal = ‖g.val.det‖₊ := by
      apply NNReal.eq
      simp [Real.norm_eq_abs]
    rw [hn, lowerBlockDensity, ENNReal.coe_mul, mul_comm]
  change (D.measure.withDensity (lowerBlockDensity d)).map e = _
  rw [map_withDensity_equiv, he]
  simp_rw [hen]
  exact withDensity_smul _ (measurable_lowerBlockDensity d)

private theorem map_rightRectangle (ν : AdditiveHaarMeasure ℝ) (g : G) :
    (rectangularMeasure ν d (r + 1)).map (fun x : X => x * g.val) =
      (‖g.val.det‖₊ ^ d)⁻¹ • rectangularMeasure ν d (r + 1) := by
  let := sigmaFinite_haar ν
  have hScale (c : ℝ) (hc : c ≠ 0) : ν.measure.map (fun x : ℝ => c * x) = (nnnormHom c)⁻¹ • ν.measure := by
    change ν.measure.map (fun x : ℝ => c • x) = _
    rw [map_addHaar_smul ν.measure hc, Module.finrank_self, pow_one, abs_inv,
      ← Real.norm_eq_abs, ← coe_nnnorm, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
    rfl
  simpa only [Matrix.one_mul, Matrix.det_one, map_one, one_pow, one_mul, Fintype.card_fin, nnnormHom_apply] using
    haarMeasure_map_rectangular ν.measure nnnormHom hScale (rectangularMeasure ν d (r + 1))
      (1 : Matrix (Fin d) (Fin d) ℝ) g.val (by simp) (determinant g).ne_zero

private theorem measurePreserving_lowerDiagonal (D : RealQuotientMeasureData r)
    (ν : AdditiveHaarMeasure ℝ) (ρ : Measure B) [SigmaFinite ρ] [ρ.IsMulRightInvariant] (g : G) (h : B) :
    MeasurePreserving (fun z : LowerBlockQuotientParameters (r + 1) d ℝ =>
      (rightTranslate N g z.1, z.2.1 * g.val, z.2.2 * h))
      (lowerBlockProduct D ν ρ) (lowerBlockProduct D ν ρ) := by
  let := sigmaFinite_measure D
  let := sigmaFinite_rect ν d (r + 1)
  have hg := (rightTranslate N g).continuous.measurable
  have hx : Measurable (fun x : X => x * g.val) := (continuous_id.matrix_mul continuous_const).measurable
  have hh := measurable_mul_const h
  change MeasurePreserving (Prod.map (rightTranslate N g)
    (Prod.map (fun x : X => x * g.val) (fun v => v * h))) _ _
  refine ⟨hg.prodMap (hx.prodMap hh), ?_⟩
  unfold lowerBlockProduct
  have hn : ‖g.val.det‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr (determinant g).ne_zero
  rw [← map_prod_map _ _ hg (hx.prodMap hh), ← map_prod_map _ _ hx hh,
    map_weightedQuotient, map_rightRectangle, map_mul_right_eq_self,
    prod_smul_left, prod_smul_left, prod_smul_right, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero d hn), one_smul]

private theorem measurePreserving_lowerShear (D : RealQuotientMeasureData r)
    (ν : AdditiveHaarMeasure ℝ) (ρ : Measure B) [SigmaFinite ρ] (y : X) :
    MeasurePreserving (fun z : LowerBlockQuotientParameters (r + 1) d ℝ =>
      (z.1, z.2.1 + z.2.2.val.val * y, z.2.2))
      (lowerBlockProduct D ν ρ) (lowerBlockProduct D ν ρ) := by
  let := sigmaFinite_measure D
  let := sigmaFinite_rect ν d (r + 1)
  let := sigmaFinite_haar ν
  have hsm : Measurable (Function.uncurry fun (b : B) (x : X) => x + b.val.val * y) :=
    (continuous_snd.add ((Units.continuous_val.comp (continuous_subtype_val.comp
      continuous_fst)).matrix_mul continuous_const)).measurable
  have hs := (MeasurePreserving.id ρ).skew_product hsm
    (Filter.Eventually.of_forall fun b =>
      (measurePreserving_add_right (rectangularMeasure ν d (r + 1)) (b.val.val * y)).map_eq)
  have hs' : MeasurePreserving (fun z : X × B => (z.1 + z.2.val.val * y, z.2))
      ((rectangularMeasure ν d (r + 1)).prod ρ) ((rectangularMeasure ν d (r + 1)).prod ρ) :=
    measurePreserving_swap.comp (hs.comp measurePreserving_swap)
  exact (MeasurePreserving.id _).prod hs'

/-- With a sigma-finite right-invariant trailing measure, the determinant-weighted
real product is invariant under the right action of every lower-block display. -/
def RealLowerBlockProductInvarianceStatement : Prop :=
  ∀ (r d : ℕ) (D : RealQuotientMeasureData r) (ν : AdditiveHaarMeasure ℝ)
    (ρ : Measure (lowerTriangularSubgroup d ℝ)) [SigmaFinite ρ] [ρ.IsMulRightInvariant],
    ∀ (g : Langlands.GeneralLinear (r + 1) ℝ) (y : Matrix (Fin d) (Fin (r + 1)) ℝ)
      (h : lowerTriangularSubgroup d ℝ),
      MeasurePreserving (lowerBlockRight g y h) (lowerBlockProduct D ν ρ) (lowerBlockProduct D ν ρ)

theorem realLowerBlockProductInvariance : RealLowerBlockProductInvarianceStatement := by
  intro r d D ν ρ _ _ g y h
  convert (measurePreserving_lowerDiagonal D ν ρ g h).comp
    (measurePreserving_lowerShear D ν ρ (y * (g⁻¹).val)) using 1
  funext z
  simp [lowerBlockRight, Matrix.add_mul, Matrix.mul_assoc]

end Langlands.Global.RankinSelbergGlobal.RealLowerBlockMeasure
