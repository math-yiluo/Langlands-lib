import Langlands.Global.RankinSelberg.RealGodementRectangularFourier
import Langlands.Global.RankinSelberg.RealJacquetConventionReduction
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # The affine column Fourier transfer in the real larger-gap unfolding -/

noncomputable section

open MeasureTheory
open scoped SchwartzMap RealInnerProductSpace NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapColumnFourier

open Langlands.LocalFactor.Archimedean (realScaledCharacter)
open ArchimedeanLocal (realFourierTransform realNormalizedAbs realSelfDualMeasure)
open RealGodement (euclideanSelfDualMeasure euclideanHaarFactor scaledEuclideanFourier
  scaledEuclideanFourier_eq_integral scaledEuclideanFourier_apply realGodementScaledProductFourier)

universe u

/-- The product of the real self-dual measures for the parameter `a`. -/
def piMeasure (ι : Type u) [Fintype ι] (a : ℝˣ) : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => (realSelfDualMeasure a).measure

/-- The positive real additive character of parameter `a`, as a complex function. -/
def psi (a : ℝˣ) (t : ℝ) : ℂ := (realScaledCharacter a).complex t

theorem psi_neg (a : ℝˣ) (t : ℝ) : psi (-a) t = psi a (-t) := by
  simp only [psi, Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, realScaledCharacter,
    Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.scale_apply, Units.val_neg, neg_mul, mul_neg]

theorem norm_psi (a : ℝˣ) (t : ℝ) : ‖psi a t‖ = 1 :=
  Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.norm_complex (realScaledCharacter a) t

theorem continuous_psi (a : ℝˣ) : Continuous (psi a) :=
  Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.continuous_complex (realScaledCharacter a)

theorem piMeasure_neg (ι : Type u) [Fintype ι] (a : ℝˣ) : piMeasure ι (-a) = piMeasure ι a := by
  unfold piMeasure
  rw [RealJacquet.selfDualMeasure_neg]

private theorem measurePreserving_toEuclidean (a : ℝˣ) (ι : Type u) [Fintype ι] :
    MeasurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ)) (piMeasure ι a)
      (euclideanSelfDualMeasure a (EuclideanSpace ℝ ι)) := by
  let c : NNReal := NNReal.sqrt ‖(a : ℝ)‖₊
  have hc : (c : ℝ) = Real.sqrt |(a : ℝ)| := by
    dsimp only [c]
    rw [Real.coe_sqrt, coe_nnnorm, Real.norm_eq_abs]
  have hFactor : (∏ _ : ι, (c : ℝ≥0∞)) = ENNReal.ofReal
      (euclideanHaarFactor a (EuclideanSpace ℝ ι)) := by
    simp only [Finset.prod_const, Finset.card_univ, euclideanHaarFactor, finrank_euclideanSpace]
    rw [← hc, ← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow]
  change MeasurePreserving _ (Measure.pi fun _ : ι => c • (volume : Measure ℝ)) _
  rw [RectangleTate.pi_smul_eq, hFactor, euclideanSelfDualMeasure]
  have h := PiLp.volume_preserving_toLp ι
  refine ⟨h.measurable, ?_⟩
  change Measure.map (WithLp.toLp 2) (_ • (volume : Measure (ι → ℝ))) = _
  rw [Measure.map_smul _ h.measurable.aemeasurable, h.map_eq]

instance (ι : Type u) [Fintype ι] (a : ℝˣ) : (piMeasure ι a).IsAddHaarMeasure := by
  unfold piMeasure
  have := (realSelfDualMeasure a).isAddHaar
  infer_instance

/-! ## Fourier transform of vectors as Schwartz functions -/

variable {m : ℕ}

/-- Euclidean coordinates for real column vectors. -/
def columnCoordinates : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
  ({ toFun := fun z i => z i
     invFun := fun x => WithLp.toLp 2 x
     left_inv := by intro z; rfl
     right_inv := by intro x; rfl
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : EuclideanSpace ℝ (Fin m) ≃ₗ[ℝ] (Fin m → ℝ)).toContinuousLinearEquiv

/-- The positive real Fourier transform of a column Schwartz function, as a Schwartz function. -/
def columnSchwartzFourier (a : ℝˣ) (Φ : 𝓢(Fin m → ℝ, ℂ)) : 𝓢(Fin m → ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ columnCoordinates.symm
    (scaledEuclideanFourier a (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ columnCoordinates Φ))

private theorem inner_columnCoordinates (z w : EuclideanSpace ℝ (Fin m)) :
    ⟪z, w⟫ = ∑ i, columnCoordinates z i * columnCoordinates w i := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm (w i) (z i)

theorem columnSchwartzFourier_apply (a : ℝˣ) (Φ : 𝓢(Fin m → ℝ, ℂ)) (y : Fin m → ℝ) :
    columnSchwartzFourier a Φ y = realFourierTransform a Φ y := by
  change scaledEuclideanFourier a (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    columnCoordinates Φ) (columnCoordinates.symm y) = _
  rw [scaledEuclideanFourier_eq_integral]
  have hPoint (z : EuclideanSpace ℝ (Fin m)) :
      realScaledCharacter a ⟪z, columnCoordinates.symm y⟫ •
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ columnCoordinates Φ) z =
      Φ (columnCoordinates z) * (realScaledCharacter a).complex
        (∑ j, columnCoordinates z j * y j) := by
    rw [inner_columnCoordinates, ContinuousLinearEquiv.apply_symm_apply]
    simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      Circle.smul_def, smul_eq_mul]
    exact mul_comm _ _
  simp only [hPoint]
  have hm := (measurePreserving_toEuclidean a (Fin m)).symm
  rw [realFourierTransform, ArchimedeanLocal.fourierTransform]
  exact hm.integral_comp' (fun x : Fin m → ℝ => Φ x * (realScaledCharacter a).complex
    (∑ j, x j * y j))

/-! ## Complementary column slices -/

section Partition

variable (p : Fin m → Prop) [DecidablePred p]

local notation "A" => {i : Fin m // p i}
local notation "B" => {i : Fin m // ¬p i}
local notation "E" => EuclideanSpace ℝ A
local notation "F" => EuclideanSpace ℝ B
local notation "P" => WithLp 2 (E × F)

/-- Assemble two complementary systems of coordinates into a column. -/
def merge (x : A → ℝ) (y : B → ℝ) : Fin m → ℝ :=
  fun i => if h : p i then x ⟨i, h⟩ else y ⟨i, h⟩

theorem merge_apply (x : A → ℝ) (y : B → ℝ) (i : Fin m) :
    merge p x y i = if h : p i then x ⟨i, h⟩ else y ⟨i, h⟩ := rfl

theorem merge_apply_left (x : A → ℝ) (y : B → ℝ) (i : A) : merge p x y i = x i := by
  simp [merge_apply, i.2]

theorem merge_apply_right (x : A → ℝ) (y : B → ℝ) (i : B) : merge p x y i = y i := by
  simp [merge_apply, i.2]

theorem continuous_merge : Continuous (fun xy : (A → ℝ) × (B → ℝ) => merge p xy.1 xy.2) := by
  apply continuous_pi
  intro i
  unfold merge
  by_cases h : p i
  · simp only [h, dite_true]
    exact (continuous_apply _).comp continuous_fst
  · simp only [h, dite_false]
    exact (continuous_apply _).comp continuous_snd

private def partitionCoordinates : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] P :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.sumCompl p).symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : A ⊕ B => ℝ))

private theorem assemble_partitionCoordinates (x : A → ℝ) (y : B → ℝ) :
    columnCoordinates ((partitionCoordinates p).symm
      (WithLp.toLp 2 (WithLp.toLp 2 x, WithLp.toLp 2 y))) = merge p x y := by
  ext i
  change ((partitionCoordinates p).symm (WithLp.toLp 2 (WithLp.toLp 2 x, WithLp.toLp 2 y))) i = _
  by_cases h : p i
  · simp [partitionCoordinates, merge, h, Equiv.piCongrLeft']
  · simp [partitionCoordinates, merge, h, Equiv.piCongrLeft']

private def partitionedSchwartz (Φ : 𝓢(Fin m → ℝ, ℂ)) : 𝓢(P, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((partitionCoordinates p).symm.toContinuousLinearEquiv.trans columnCoordinates) Φ

private theorem scaledEuclideanFourier_partition (a : ℝˣ) (Φ : 𝓢(Fin m → ℝ, ℂ)) (z : P) :
    scaledEuclideanFourier a (partitionedSchwartz p Φ) z =
      columnSchwartzFourier a Φ (columnCoordinates ((partitionCoordinates p).symm z)) := by
  let J := (partitionCoordinates p).symm
  let f := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ columnCoordinates Φ
  have hFactor : euclideanHaarFactor a P = euclideanHaarFactor a (EuclideanSpace ℝ (Fin m)) := by
    simp only [euclideanHaarFactor, J.toLinearEquiv.finrank_eq]
  have hf : (partitionedSchwartz p Φ : P → ℂ) = (f : EuclideanSpace ℝ (Fin m) → ℂ) ∘ J := rfl
  change scaledEuclideanFourier a (partitionedSchwartz p Φ) z = scaledEuclideanFourier a f (J z)
  rw [scaledEuclideanFourier_apply, scaledEuclideanFourier_apply, hFactor,
    SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_coe, hf,
    Real.fourierInv_comp_linearIsometry, map_smul]

private theorem inner_entry_coordinates {ι : Type u} [Fintype ι] (x z : ι → ℝ) :
    ⟪WithLp.toLp 2 x, WithLp.toLp 2 z⟫ = ∑ i, x i * z i := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm (z i) (x i)

/-- Complementary affine slices of a column Schwartz function and of its positive Fourier
transform satisfy Fourier inversion. -/
theorem columnSlices (a : ℝˣ) (Φ : 𝓢(Fin m → ℝ, ℂ)) (x₀ : A → ℝ) (y₀ : B → ℝ) :
    let f := fun x : A → ℝ => Φ (merge p x y₀) * psi a (∑ i, x i * x₀ i)
    let g := fun y : B → ℝ => realFourierTransform a Φ (merge p x₀ y) *
      psi a (-(∑ i, y i * y₀ i))
    Integrable f (piMeasure A a) ∧ Integrable g (piMeasure B a) ∧
      (∫ y, g y ∂piMeasure B a) = ∫ x, f x ∂piMeasure A a := by
  dsimp only
  let Ψ := partitionedSchwartz p Φ
  obtain ⟨hL, hR, hEq⟩ := realGodementScaledProductFourier E F a Ψ
    (WithLp.toLp 2 x₀) (WithLp.toLp 2 y₀)
  let f := fun x : E => realScaledCharacter a ⟪x, WithLp.toLp 2 x₀⟫ •
    Ψ (WithLp.toLp 2 (x, WithLp.toLp 2 y₀))
  let g := fun y : F => realScaledCharacter a (-⟪y, WithLp.toLp 2 y₀⟫) •
    scaledEuclideanFourier a Ψ (WithLp.toLp 2 (WithLp.toLp 2 x₀, y))
  have hf (x : A → ℝ) : f (WithLp.toLp 2 x) = Φ (merge p x y₀) * psi a (∑ i, x i * x₀ i) := by
    simp only [f, inner_entry_coordinates]
    change realScaledCharacter a (∑ i, x i * x₀ i) •
      Φ (columnCoordinates ((partitionCoordinates p).symm
        (WithLp.toLp 2 (WithLp.toLp 2 x, WithLp.toLp 2 y₀)))) = _
    rw [assemble_partitionCoordinates]
    exact mul_comm _ _
  have hg (y : B → ℝ) : g (WithLp.toLp 2 y) =
      realFourierTransform a Φ (merge p x₀ y) * psi a (-(∑ i, y i * y₀ i)) := by
    simp only [g, Ψ, inner_entry_coordinates, scaledEuclideanFourier_partition,
      assemble_partitionCoordinates, columnSchwartzFourier_apply]
    exact mul_comm _ _
  have hA := measurePreserving_toEuclidean a A
  have hB := measurePreserving_toEuclidean a B
  refine ⟨?_, ?_, ?_⟩
  · exact (hA.integrable_comp_of_integrable (show Integrable f _ from hL)).congr
      (Filter.Eventually.of_forall hf)
  · exact (hB.integrable_comp_of_integrable (show Integrable g _ from hR)).congr
      (Filter.Eventually.of_forall hg)
  · calc
      _ = ∫ y : B → ℝ, g (WithLp.toLp 2 y) ∂piMeasure B a :=
        (integral_congr_ae (Filter.Eventually.of_forall hg)).symm
      _ = ∫ y : F, g y ∂euclideanSelfDualMeasure a F := hB.integral_comp' g
      _ = ∫ x : E, f x ∂euclideanSelfDualMeasure a E := hEq
      _ = ∫ x : A → ℝ, f (WithLp.toLp 2 x) ∂piMeasure A a := (hA.integral_comp' f).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall hf)

end Partition

/-! ## Linear changes of the column -/

variable {r : ℕ}
local notation "V" => Fin (r + 1) → ℝ
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ

private def columnLE (g : G) : V ≃ₗ[ℝ] V where
  toFun x := g.val.mulVec x
  invFun x := g⁻¹.val.mulVec x
  left_inv x := by
    change g⁻¹.val.mulVec (g.val.mulVec x) = x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv x := by
    change g.val.mulVec (g⁻¹.val.mulVec x) = x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  map_add' x y := Matrix.mulVec_add _ _ _
  map_smul' c x := Matrix.mulVec_smul _ _ _

private def columnCLE (g : G) : V ≃L[ℝ] V := (columnLE g).toContinuousLinearEquiv

/-- Pull back a column Schwartz function by matrix multiplication. -/
def pullColumn (g : G) (Φ : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (columnCLE g) Φ

@[simp]
theorem pullColumn_apply (g : G) (Φ : 𝓢(V, ℂ)) (x : V) :
    pullColumn g Φ x = Φ (g.val.mulVec x) := rfl

/-- Integration against the self-dual product measure after a linear change of variables. -/
theorem integral_mulVec (a : ℝˣ) (g : G) (K : V → ℂ) :
    (∫ x, K (g.val.mulVec x) ∂piMeasure (Fin (r + 1)) a) =
      ((realNormalizedAbs g.val.det)⁻¹ : ℝ) • ∫ x, K x ∂piMeasure (Fin (r + 1)) a := by
  let μ := piMeasure (Fin (r + 1)) a
  let f : V →ₗ[ℝ] V := Matrix.toLin' g.val
  have hdet : LinearMap.det f ≠ 0 := by
    rw [LinearMap.det_toLin']
    exact g.det_ne_zero
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
  have he : (fun x : V => K (g.val.mulVec x)) = K ∘ f := by
    funext x
    rfl
  have hf : MeasurableEmbedding f :=
    (columnCLE g).toHomeomorph.measurableEmbedding
  rw [he]
  change ∫ x, K (f x) ∂μ = _
  rw [← hf.integral_map K, hmap, integral_smul_measure, LinearMap.det_toLin',
    ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
  rfl

/-- Full column Fourier transformation moves a matrix to the inverse transpose and contributes
its additive determinant Jacobian. -/
theorem fourier_pullColumn (a : ℝˣ) (g : G) (Φ : 𝓢(V, ℂ)) (y : V) :
    realFourierTransform a (pullColumn g Φ) y =
      ((realNormalizedAbs g.val.det)⁻¹ : ℝ) •
        realFourierTransform a Φ (g⁻¹.val.transpose.mulVec y) := by
  let z := g⁻¹.val.transpose.mulVec y
  let K (x : V) := Φ x * psi a (∑ i, x i * z i)
  have hp (x : V) : (∑ i, g.val.mulVec x i * z i) = ∑ i, x i * y i := by
    change dotProduct (g.val.mulVec x) (g⁻¹.val.transpose.mulVec y) = dotProduct x y
    rw [Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mulVec, dotProduct_comm]
  calc
    realFourierTransform a (pullColumn g Φ) y = ∫ x, K (g.val.mulVec x) ∂piMeasure _ a := by
      simp only [realFourierTransform, ArchimedeanLocal.fourierTransform, pullColumn_apply, K, hp,
        psi]
      rfl
    _ = ((realNormalizedAbs g.val.det)⁻¹ : ℝ) • ∫ x, K x ∂piMeasure _ a := integral_mulVec a g K
    _ = _ := by
      simp only [realFourierTransform, ArchimedeanLocal.fourierTransform, K, psi]
      rfl

variable (p : Fin (r + 1) → Prop) [DecidablePred p]

local notation "U" => {i : Fin (r + 1) // p i} → ℝ
local notation "L" => {i : Fin (r + 1) // ¬ p i} → ℝ

/-- Fourier exchange between complementary affine column slices after an arbitrary invertible
real change of coordinates. -/
def RealGapColumnFourierStatement : Prop :=
  ∀ (a : ℝˣ) (g : G) (Φ : 𝓢(V, ℂ)) (α : U) (β : L),
    let P (x : U) := Φ (g.val.mulVec (merge p x β)) * psi a (∑ i, x i * α i)
    let Q (y : L) := realFourierTransform a Φ (g⁻¹.val.transpose.mulVec (merge p α y)) *
      psi (-a) (∑ i, y i * β i)
    Integrable P (piMeasure _ a) ∧ Integrable Q (piMeasure _ a) ∧
    (∫ x, P x ∂piMeasure _ a) =
      ((realNormalizedAbs g.val.det)⁻¹ : ℝ) • ∫ y, Q y ∂piMeasure _ a

theorem realGapColumnFourier : RealGapColumnFourierStatement (r := r) p := by
  intro a g Φ α β
  obtain ⟨hf, hg, hEq⟩ := columnSlices p a (pullColumn g Φ) α β
  have hQ (y : L) : realFourierTransform a (pullColumn g Φ) (merge p α y) * psi a (-(∑ i, y i * β i)) =
      ((realNormalizedAbs g.val.det)⁻¹ : ℝ) •
        (realFourierTransform a Φ (g⁻¹.val.transpose.mulVec (merge p α y)) *
          psi (-a) (∑ i, y i * β i)) := by
    rw [fourier_pullColumn, psi_neg, smul_mul_assoc]
  have hc : ((realNormalizedAbs g.val.det)⁻¹ : ℝ) ≠ 0 :=
    inv_ne_zero (abs_pos.mpr g.det_ne_zero).ne'
  refine ⟨hf, ?_, ?_⟩
  · have h := hg.smul ((((realNormalizedAbs g.val.det)⁻¹ : ℝ)⁻¹ : ℝ) : ℂ)
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.smul_apply, hQ, Complex.real_smul, smul_eq_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hc, Complex.ofReal_one, one_mul]
  · calc (∫ x, Φ (g.val.mulVec (merge p x β)) * psi a (∑ i, x i * α i) ∂piMeasure _ a)
          = ∫ y, realFourierTransform a (pullColumn g Φ) (merge p α y) *
              psi a (-(∑ i, y i * β i)) ∂piMeasure _ a := hEq.symm
      _ = ∫ y, ((realNormalizedAbs g.val.det)⁻¹ : ℝ) •
            (realFourierTransform a Φ (g⁻¹.val.transpose.mulVec (merge p α y)) *
              psi (-a) (∑ i, y i * β i)) ∂piMeasure _ a :=
          integral_congr_ae (Filter.Eventually.of_forall hQ)
      _ = _ := integral_smul _ _

/-- Independent column slices can be transferred at once. Each contributes the same
determinant factor for the matrix used in all columns. -/
theorem realGapColumnFourierProduct {J : Type*} [Fintype J]
    (part : J → Fin (r + 1) → Prop) [∀ j, DecidablePred (part j)]
    (a : ℝˣ) (g : G) (Φ : J → 𝓢(V, ℂ))
    (α : ∀ j, {i // part j i} → ℝ) (β : ∀ j, {i // ¬ part j i} → ℝ) :
    let P (j : J) (x : {i // part j i} → ℝ) :=
      Φ j (g.val.mulVec (merge (part j) x (β j))) * psi a (∑ i, x i * α j i)
    let Q (j : J) (y : {i // ¬ part j i} → ℝ) :=
      realFourierTransform a (Φ j) (g⁻¹.val.transpose.mulVec (merge (part j) (α j) y)) *
        psi (-a) (∑ i, y i * β j i)
    Integrable (fun x => ∏ j, P j (x j)) (Measure.pi fun j : J => piMeasure {i // part j i} a) ∧
    Integrable (fun y => ∏ j, Q j (y j)) (Measure.pi fun j : J => piMeasure {i // ¬ part j i} a) ∧
    (∫ x, ∏ j, P j (x j) ∂Measure.pi fun j : J => piMeasure {i // part j i} a) =
      (((realNormalizedAbs g.val.det)⁻¹ : ℝ) : ℂ) ^ Fintype.card J *
        ∫ y, ∏ j, Q j (y j) ∂Measure.pi fun j : J => piMeasure {i // ¬ part j i} a := by
  intro P Q
  have h j := realGapColumnFourier (part j) a g (Φ j) (α j) (β j)
  refine ⟨Integrable.fintype_prod_dep (fun j => (h j).1),
    Integrable.fintype_prod_dep (fun j => (h j).2.1), ?_⟩
  rw [integral_fintype_prod_eq_prod P, integral_fintype_prod_eq_prod Q]
  have hIntegral (j : J) : (∫ x, P j x ∂piMeasure {i // part j i} a) =
      ((realNormalizedAbs g.val.det)⁻¹ : ℝ) • ∫ y, Q j y ∂piMeasure {i // ¬ part j i} a :=
    (h j).2.2
  simp_rw [hIntegral, Complex.real_smul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end Langlands.Global.RankinSelbergGlobal.RealGapColumnFourier
