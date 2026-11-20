import Langlands.Global.RankinSelberg.RealGodementColumnReflection
import Langlands.Global.RankinSelberg.RealGodementLastColumn
import Langlands.Representation.Archimedean.RealLeviChartIntegrable

/-! # The open-cell Jacquet integral of a real Godement section -/

noncomputable section

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Whittaker
open Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory MeasureTheory.Measure Matrix
open scoped BigOperators ENNReal Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (t : ℕ) : MeasurableSpace (LeftUnipotentQuotient t ℝ) := borel _
private local instance (t : ℕ) : BorelSpace (LeftUnipotentQuotient t ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "m" => (t + 1)
local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "N" => GeneralLinear.upperUnipotent (t + 1) ℝ
local notation "U" => GeneralLinear.upperUnipotent (t + 2) ℝ
local notation "V" => (Fin (t + 1) → ℝ)
local notation "M" => Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ

/-- The positive-phase Jacquet integrand on the upper unipotent open cell. -/
def additiveJacquetKernel (a : ℝˣ) (f : G → ℂ) (g : G) (u : N) : ℂ :=
  f (weylLong m ℝ * u.val * g) * (standardCharacter (realScaledCharacter a) t u : ℂ)

/-- The Jacquet integral on the open cell with the specified upper entry measure. -/
def additiveJacquetIntegral (a : ℝˣ) (f : G → ℂ) (g : G) : ℂ :=
  ∫ u, additiveJacquetKernel a f g u ∂upperStepHaar t a

/-- The Jacquet integrand with the inner Godement section expanded as a group integral. -/
def godementOpenCellKernel (a : ℝˣ) (c : RealCharacterData) (f : G → ℂ)
    (Φ : 𝓢(X, ℂ)) (g : H) (p : U × G) : ℂ :=
  let k := weylLong (m + 1) ℝ * p.1.val * g
  determinantWeight c ((m : ℂ) / 2) k *
    (f p.2⁻¹ * determinantWeight c (((m : ℂ) + 1) / 2) p.2 * Φ (rowPoint p.2.val k)) *
    (standardCharacter (realScaledCharacter a) (t + 1) p.1 : ℂ)

private theorem integral_godementOpenCellKernel (μ : Measure G) (a : ℝˣ)
    (c : RealCharacterData) (f : G → ℂ) (Φ : 𝓢(X, ℂ)) (g : H) (u : U) :
    (∫ h, godementOpenCellKernel a c f Φ g (u, h) ∂μ) =
      additiveJacquetKernel a (sectionValue μ c f Φ) g u := by
  simp only [godementOpenCellKernel, additiveJacquetKernel, sectionValue, innerIntegral,
    integral_mul_const, integral_const_mul]
  rw [show ((t : ℂ) + 1) = ((t + 1 : ℕ) : ℂ) from (Nat.cast_succ t).symm]
  rfl

private def conjugatedUnipotent (u : N) : G :=
  weylLong m ℝ * u.val * weylLong m ℝ

private theorem conjugatedUnipotent_det (u : N) : determinant (conjugatedUnipotent u) = 1 := by
  have hu : determinant u.val = 1 := Units.ext (Langlands.RankinSelberg.unipotent_det u)
  rw [conjugatedUnipotent, map_mul, map_mul, hu, mul_one, ← map_mul, weylLong_mul_self, map_one]

private theorem conjugatedUnipotent_mulVec_zero (u : N) (y : V) :
    (conjugatedUnipotent u).val.mulVec y 0 = y 0 := by
  unfold Matrix.mulVec dotProduct
  rw [Finset.sum_eq_single 0]
  · change (conjugatedUnipotent u).val 0 0 * y 0 = y 0
    rw [conjugatedUnipotent, weylLong_conjugate_entry, UpperUnipotent.entry_diag, one_mul]
  · intro i _ hi
    change (conjugatedUnipotent u).val 0 i * y i = 0
    rw [conjugatedUnipotent, weylLong_conjugate_entry, UpperUnipotent.entry_eq_zero]
    · exact zero_mul _
    · exact Fin.rev_lt_rev.mpr (Fin.pos_iff_ne_zero.mpr hi)
  · simp

private theorem continuous_conjugatedUnipotent : Continuous (conjugatedUnipotent (t := t)) :=
  (continuous_const.mul continuous_subtype_val).mul continuous_const

private theorem measurePreserving_column_mulVec (a : ℝˣ) (u : N) :
    MeasurePreserving (fun y : V => (conjugatedUnipotent u).val *ᵥ y)
      (rowMeasure (realSelfDualMeasure a) m) (rowMeasure (realSelfDualMeasure a) m) := by
  have hdet : (conjugatedUnipotent u).val.det = 1 :=
    congrArg Units.val (conjugatedUnipotent_det u)
  have h := Langlands.Archimedean.RealLeviChartIntegrable.measurePreserving_mulVec
    (show |(conjugatedUnipotent u).val.det| = 1 by rw [hdet, abs_one])
  let r : ℝ≥0 := NNReal.sqrt ‖(a : ℝ)‖₊
  change MeasurePreserving _ (Measure.pi (fun _ : Fin m => r • (volume : Measure ℝ)))
    (Measure.pi (fun _ : Fin m => r • (volume : Measure ℝ)))
  rw [RectangleTate.pi_smul_eq]
  refine ⟨h.measurable, ?_⟩
  rw [Measure.map_smul _ h.measurable.aemeasurable]
  change (∏ _ : Fin m, (r : ℝ≥0∞)) •
    Measure.map (fun y : V => (conjugatedUnipotent u).val *ᵥ y) (volume : Measure V) =
    (∏ _ : Fin m, (r : ℝ≥0∞)) • (volume : Measure V)
  rw [h.map_eq]

variable (t) in
private def columnChange :
    (N × (G × V)) ≃ᵐ (N × (G × V)) where
  toFun p := (p.1, (p.2.1 * (conjugatedUnipotent p.1)⁻¹, (conjugatedUnipotent p.1).val *ᵥ p.2.2))
  invFun p := (p.1, (p.2.1 * conjugatedUnipotent p.1, (conjugatedUnipotent p.1)⁻¹.val *ᵥ p.2.2))
  left_inv := by
    rintro ⟨u, h, y⟩
    simp only [mul_assoc, inv_mul_cancel, mul_one, Matrix.mulVec_mulVec, ← Units.val_mul,
      Units.val_one, Matrix.one_mulVec]
  right_inv := by
    rintro ⟨u, h, y⟩
    simp only [mul_assoc, mul_inv_cancel, mul_one, Matrix.mulVec_mulVec, ← Units.val_mul,
      Units.val_one, Matrix.one_mulVec]
  measurable_toFun := by
    have hu := (continuous_conjugatedUnipotent (t := t)).comp (continuous_fst (Y := G × V))
    exact (continuous_fst.prodMk <|
      (continuous_snd.fst.mul hu.inv).prodMk
        ((Units.continuous_val.comp hu).matrix_mulVec continuous_snd.snd)).measurable
  measurable_invFun := by
    have hu := (continuous_conjugatedUnipotent (t := t)).comp (continuous_fst (Y := G × V))
    exact (continuous_fst.prodMk <|
      (continuous_snd.fst.mul hu).prodMk
        ((Units.continuous_val.comp hu.inv).matrix_mulVec continuous_snd.snd)).measurable

private theorem measurePreserving_columnChange (μ : Measure G) [SigmaFinite μ]
    [μ.IsMulRightInvariant] (a : ℝˣ) :
    MeasurePreserving (columnChange t)
      ((upperStepHaar t a).prod (μ.prod (rowMeasure (realSelfDualMeasure a) m)))
      ((upperStepHaar t a).prod (μ.prod (rowMeasure (realSelfDualMeasure a) m))) := by
  let : SigmaFinite (upperStepHaar t a) := upperStepHaar_sigmaFinite t a
  refine (MeasurePreserving.id (upperStepHaar t a)).skew_product
    (g := fun (u : N) (p : G × V) =>
      (p.1 * (conjugatedUnipotent u)⁻¹, (conjugatedUnipotent u).val *ᵥ p.2))
    (columnChange t).measurable.snd (Filter.Eventually.of_forall fun u => ?_)
  exact ((measurePreserving_mul_right μ (conjugatedUnipotent u)⁻¹).prod
    (measurePreserving_column_mulVec a u)).map_eq

variable (t) in
private def jacquetProductChart :
    ((G × V) × N) ≃ᵐ (U × G) :=
  MeasurableEquiv.prodComm.trans ((columnChange t).trans
    (MeasurableEquiv.prodAssoc.symm.trans (MeasurableEquiv.prodComm.trans
      (MeasurableEquiv.prodAssoc.symm.trans
        ((lastColumnChart t).prodCongr (MeasurableEquiv.refl G))))))

private theorem measurePreserving_jacquetProductChart (μ : Measure G) [SigmaFinite μ]
    [μ.IsMulRightInvariant] (a : ℝˣ) :
    MeasurePreserving (jacquetProductChart t)
      ((μ.prod (rowMeasure (realSelfDualMeasure a) m)).prod (upperStepHaar t a))
      ((upperStepHaar (t + 1) a).prod μ) := by
  let ν := rowMeasure (realSelfDualMeasure a) m
  let η := upperStepHaar t a
  let : SigmaFinite η := upperStepHaar_sigmaFinite t a
  exact ((measurePreserving_lastColumnChart t a).prod (MeasurePreserving.id μ)).comp
    (((measurePreserving_prodAssoc ν η μ).symm MeasurableEquiv.prodAssoc).comp
      ((measurePreserving_swap (μ := η.prod μ) (ν := ν)).comp
        (((measurePreserving_prodAssoc η μ ν).symm MeasurableEquiv.prodAssoc).comp
          ((measurePreserving_columnChange μ a).comp measurePreserving_swap))))

private def separatedKernel (a : ℝˣ) (c : RealCharacterData) (f : G → ℂ)
    (Φ : 𝓢(X, ℂ)) (g : H) (p : (G × V) × N) : ℂ :=
  let (h, y) := p.1
  determinantWeight c ((m : ℂ) / 2) g *
    (Φ (h.val * joinFirstColumn y 1 * g.val) * (realScaledCharacter a).complex (y 0)) *
    additiveJacquetKernel a f (columnRepresentative h) p.2 *
    determinantWeight c (((m : ℂ) + 1) / 2) h

private theorem determinantWeight_congr {n : ℕ} (c : RealCharacterData) (z : ℂ)
    {g g' : Langlands.GeneralLinear n ℝ} (he : determinant g = determinant g') :
    determinantWeight c z g = determinantWeight c z g' := by
  unfold determinantWeight
  simp only [MonoidHom.comp_apply]
  exact congrArg _ he

private theorem conjugatedUnipotent_joinFirstColumn (u : N) (y : V) :
    (conjugatedUnipotent u).val * joinFirstColumn y 1 =
      joinFirstColumn ((conjugatedUnipotent u).val *ᵥ y) (conjugatedUnipotent u).val := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, joinFirstColumn_zero]
  · simpa only [Matrix.mul_apply, joinFirstColumn_succ] using
      congrArg (fun A : M => A i k) (Matrix.mul_one (conjugatedUnipotent u).val)

private theorem godementOpenCellKernel_comp_chart (a : ℝˣ) (c : RealCharacterData)
    (f : G → ℂ) (Φ : 𝓢(X, ℂ)) (g : H) (p : (G × V) × N) :
    godementOpenCellKernel a c f Φ g (jacquetProductChart t p) =
      separatedKernel a c f Φ (weylLong (m + 1) ℝ * g) p := by
  obtain ⟨⟨h, y⟩, u⟩ := p
  let B := conjugatedUnipotent u
  let x := B.val *ᵥ y
  let v := lastColumnChart t (x, u)
  let w := weylLong (m + 1) ℝ
  let k := w * v.val * g
  have hdg : determinant k = determinant (w * g) := by
    have hv : determinant v.val = 1 := Units.ext (Langlands.RankinSelberg.unipotent_det v)
    rw [show k = w * v.val * g from rfl, map_mul, map_mul, hv, mul_one, map_mul]
  have hB : B = conjugatedUnipotent u := rfl
  have hdh : determinant (h * B⁻¹) = determinant h := by
    rw [map_mul, map_inv, hB, conjugatedUnipotent_det u, inv_one, mul_one]
  have harg : (h * B⁻¹)⁻¹ = weylLong m ℝ * u.val * columnRepresentative h := by
    rw [_root_.mul_inv_rev, inv_inv, columnRepresentative, hB, conjugatedUnipotent, mul_assoc]
  have hrect : rowPoint (h * B⁻¹).val k = h.val * joinFirstColumn y 1 * (w * g).val := by
    rw [rowPoint, show k = w * v.val * g from rfl, lastRows_lastColumnChart x u g,
      ← Matrix.mul_assoc]
    change ((h * B⁻¹).val * joinFirstColumn x B.val) * (w * g).val = _
    rw [show joinFirstColumn x B.val = B.val * joinFirstColumn y 1 from
      (conjugatedUnipotent_joinFirstColumn u y).symm, ← Matrix.mul_assoc, ← Units.val_mul,
      _root_.mul_assoc, inv_mul_cancel, mul_one]
  have hx : x 0 = y 0 := conjugatedUnipotent_mulVec_zero u y
  change godementOpenCellKernel a c f Φ g (v, h * B⁻¹) = _
  unfold godementOpenCellKernel separatedKernel additiveJacquetKernel
  dsimp only
  rw [determinantWeight_congr c _ hdg, determinantWeight_congr c _ hdh, harg, hrect,
    standardCharacter_lastColumnChart a x u, hx]
  ring

private theorem integral_separatedKernel (a : ℝˣ) (c : RealCharacterData)
    (f : G → ℂ) (Φ : 𝓢(X, ℂ)) (g : H) (h : G) :
    (∫ y : V, ∫ u : N, separatedKernel a c f Φ g ((h, y), u) ∂upperStepHaar t a
      ∂rowMeasure (realSelfDualMeasure a) m) =
      stepGroupIntegrand a Φ (additiveJacquetIntegral a f) c g h := by
  simp only [separatedKernel, integral_mul_const, integral_const_mul, stepGroupIntegrand,
    stepColumnSlice, additiveJacquetIntegral]
  rw [show (((t + 2 : ℕ) : ℂ) / 2) = ((m : ℂ) + 1) / 2 by push_cast; ring]

/-- On the domain of joint absolute integrability the open-cell integral of the
Godement section is exactly the first-column formula of the lower Jacquet integral. -/
def RealGodementAdditiveJacquetStatement : Prop :=
  ∀ (t : ℕ) (D : RealQuotientMeasureData t) (a : ℝˣ) (c : RealCharacterData)
    (f : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ))
    (g : Langlands.GeneralLinear (t + 2) ℝ),
    Integrable (godementOpenCellKernel a c f Φ g) ((upperStepHaar (t + 1) a).prod D.groupHaar) →
    Integrable (additiveJacquetKernel a (sectionValue D.groupHaar c f Φ) g) (upperStepHaar (t + 1) a) ∧
    Integrable (stepGroupIntegrand a Φ (additiveJacquetIntegral a f) c (weylLong (t + 2) ℝ * g))
      D.groupHaar ∧
    additiveJacquetIntegral a (sectionValue D.groupHaar c f Φ) g =
      godementColumnValue D a Φ (additiveJacquetIntegral a f) c (weylLong (t + 2) ℝ * g)

theorem realGodementAdditiveJacquet : RealGodementAdditiveJacquetStatement := by
  intro t D a c f Φ g hJoint
  let μ := D.groupHaar
  let ν := rowMeasure (realSelfDualMeasure a) (t + 1)
  let η := upperStepHaar t a
  let η' := upperStepHaar (t + 1) a
  let : LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (t + 1) → ℝ))
  let : LocallyCompactSpace (Langlands.GeneralLinear (t + 1) ℝ) :=
    Units.isOpenEmbedding_val.locallyCompactSpace
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : SigmaFinite D.groupHaar := inferInstance
  let : SigmaFinite μ := ‹SigmaFinite D.groupHaar›
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  let : SigmaFinite η := upperStepHaar_sigmaFinite t a
  let : SigmaFinite η' := upperStepHaar_sigmaFinite (t + 1) a
  let g' := weylLong (t + 2) ℝ * g
  let S := separatedKernel a c f Φ g'
  have hChart := measurePreserving_jacquetProductChart μ a
  have hPoint := godementOpenCellKernel_comp_chart a c f Φ g
  have hS : Integrable S ((μ.prod ν).prod η) :=
    (hChart.integrable_comp_of_integrable hJoint).congr (Filter.Eventually.of_forall hPoint)
  have hEval := integral_separatedKernel a c f Φ g'
  refine ⟨hJoint.integral_prod_left.congr
    (Filter.Eventually.of_forall (integral_godementOpenCellKernel μ a c f Φ g)),
    hS.integral_prod_left.integral_prod_left.congr (Filter.Eventually.of_forall hEval), ?_⟩
  calc
    _ = ∫ p, godementOpenCellKernel a c f Φ g p ∂η'.prod μ := by
      rw [additiveJacquetIntegral, integral_prod _ hJoint]
      exact integral_congr_ae (Filter.Eventually.of_forall
        fun u => (integral_godementOpenCellKernel μ a c f Φ g u).symm)
    _ = ∫ p, S p ∂(μ.prod ν).prod η := by
      rw [← hChart.integral_comp' (godementOpenCellKernel a c f Φ g)]
      exact integral_congr_ae (Filter.Eventually.of_forall hPoint)
    _ = ∫ h, stepGroupIntegrand a Φ (additiveJacquetIntegral a f) c g' h ∂μ := by
      rw [integral_prod _ hS, integral_prod _ hS.integral_prod_left]
      exact integral_congr_ae (Filter.Eventually.of_forall hEval)
    _ = _ := by
      simp only [stepGroupIntegrand_eq_columnMellin, integral_const_mul, godementColumnValue]
      rfl

end Langlands.Global.RankinSelbergGlobal.RealGodement
