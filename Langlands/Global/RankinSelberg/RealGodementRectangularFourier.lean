import Langlands.Global.RankinSelberg.RealGodementScaledFourier
import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Global.RankinSelberg.RectangleTateMeasure
import Langlands.HarmonicAnalysis.RectangularFourier

/-! # Complementary real rectangular affine Fourier slices -/

noncomputable section

open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open MeasureTheory
open scoped Matrix.Norms.Operator FourierTransform RealInnerProductSpace SchwartzMap NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

universe u

private theorem measurePreserving_toEuclidean (a : ℝˣ) (ι : Type u) [Fintype ι] :
    MeasurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ))
      (Measure.pi fun _ : ι => (realSelfDualMeasure a).measure)
      (euclideanSelfDualMeasure a (EuclideanSpace ℝ ι)) := by
  let c : NNReal := NNReal.sqrt ‖(a : ℝ)‖₊
  have hc : (c : ℝ) = Real.sqrt |(a : ℝ)| := by
    dsimp only [c]
    rw [Real.coe_sqrt, coe_nnnorm, Real.norm_eq_abs]
  have hFactor : (∏ _ : ι, (c : ℝ≥0∞)) = ENNReal.ofReal
      (euclideanHaarFactor a (EuclideanSpace ℝ ι)) := by
    simp only [Finset.prod_const, Finset.card_univ, euclideanHaarFactor, finrank_euclideanSpace]
    rw [← hc, ← NNReal.coe_pow,
      ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow]
  change MeasurePreserving _ (Measure.pi fun _ : ι => c • (volume : Measure ℝ)) _
  rw [RectangleTate.pi_smul_eq, hFactor, euclideanSelfDualMeasure]
  have h := PiLp.volume_preserving_toLp ι
  refine ⟨h.measurable, ?_⟩
  change Measure.map (WithLp.toLp 2) (_ • (volume : Measure (ι → ℝ))) = _
  rw [Measure.map_smul _ h.measurable.aemeasurable, h.map_eq]

variable {r s : ℕ}

local notation "I" => Fin r × Fin s
local notation "X" => Matrix (Fin r) (Fin s) ℝ
local notation "V" => EuclideanSpace ℝ I

/-- Euclidean coordinates for the rectangular matrix entries. -/
def rectangularCoordinates : V ≃L[ℝ] X :=
  ({ toFun := fun z i j => z (i, j)
     invFun := fun x => WithLp.toLp 2 (fun q : I => x q.1 q.2)
     left_inv := by intro z; rfl
     right_inv := by intro x; rfl
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : V ≃ₗ[ℝ] X).toContinuousLinearEquiv

private theorem measurePreserving_rectangularCoordinates (a : ℝˣ) :
    MeasurePreserving (rectangularCoordinates (r := r) (s := s)).toHomeomorph.toMeasurableEquiv
      (euclideanSelfDualMeasure a V) (Langlands.RankinSelberg.rectangularMeasure (realSelfDualMeasure a) r s) := by
  exact (RectangleTate.measurePreserving_uncurry
    (fun (_ : Fin r) (_ : Fin s) => (realSelfDualMeasure a).measure)).symm.comp
      (measurePreserving_toEuclidean a I).symm

private theorem inner_rectangularCoordinates (z w : V) :
    inner ℝ z w = rectangularPairing (rectangularCoordinates z) (rectangularCoordinates w) := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, rectangularPairing]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change w (i, j) * z (i, j) = z (i, j) * w (i, j)
  exact mul_comm _ _

/-- The positive real rectangular Fourier transform, as a Schwartz function. -/
def realRectangularSchwartzFourier (a : ℝˣ) (Φ : 𝓢(X, ℂ)) : 𝓢(X, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ rectangularCoordinates.symm
    (scaledEuclideanFourier a (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ rectangularCoordinates Φ))

theorem realRectangularSchwartzFourier_apply (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (y : X) :
    realRectangularSchwartzFourier a Φ y =
      rectangularFourierIntegral (realScaledCharacter a) (realSelfDualMeasure a) Φ y := by
  change scaledEuclideanFourier a (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    rectangularCoordinates Φ) (rectangularCoordinates.symm y) = _
  rw [scaledEuclideanFourier_eq_integral]
  have hPoint (z : V) :
      realScaledCharacter a (inner ℝ z (rectangularCoordinates.symm y)) •
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ rectangularCoordinates Φ) z =
      Φ (rectangularCoordinates z) * (realScaledCharacter a).complex
        (rectangularPairing (rectangularCoordinates z) y) := by
    rw [inner_rectangularCoordinates, ContinuousLinearEquiv.apply_symm_apply]
    simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      Circle.smul_def, smul_eq_mul]
    exact mul_comm _ _
  simp only [hPoint, rectangularFourierIntegral]
  exact (measurePreserving_rectangularCoordinates (r := r) (s := s) a).integral_comp'
    (fun x : X => Φ x * (realScaledCharacter a).complex (rectangularPairing x y))

section Partition

variable (p : Fin r × Fin s → Prop) [DecidablePred p]

local notation "A" => {q : I // p q}
local notation "B" => {q : I // ¬p q}
local notation "E" => EuclideanSpace ℝ A
local notation "F" => EuclideanSpace ℝ B
local notation "P" => WithLp 2 (E × F)

private def partitionCoordinates : V ≃ₗᵢ[ℝ] P :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.sumCompl p).symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : A ⊕ B => ℝ))

/-- Assemble two disjoint systems of entries into a rectangle. -/
def joinRectangularCoordinates (x : A → ℝ) (y : B → ℝ) : X :=
  fun i j => if h : p (i, j) then x ⟨(i, j), h⟩ else y ⟨(i, j), h⟩

private theorem assemble_partitionCoordinates (x : A → ℝ) (y : B → ℝ) :
    rectangularCoordinates ((partitionCoordinates p).symm
      (WithLp.toLp 2 (WithLp.toLp 2 x, WithLp.toLp 2 y))) = joinRectangularCoordinates p x y := by
  ext i j
  change ((partitionCoordinates p).symm (WithLp.toLp 2 (WithLp.toLp 2 x, WithLp.toLp 2 y)))
    (i, j) = _
  by_cases h : p (i, j)
  · simp [partitionCoordinates, joinRectangularCoordinates, h, Equiv.piCongrLeft']
  · simp [partitionCoordinates, joinRectangularCoordinates, h, Equiv.piCongrLeft']

private def partitionedSchwartz (Φ : 𝓢(X, ℂ)) : 𝓢(P, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((partitionCoordinates p).symm.toContinuousLinearEquiv.trans rectangularCoordinates) Φ

private theorem scaledEuclideanFourier_partition (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (z : P) :
    scaledEuclideanFourier a (partitionedSchwartz p Φ) z =
      realRectangularSchwartzFourier a Φ (rectangularCoordinates ((partitionCoordinates p).symm z)) := by
  let J := (partitionCoordinates p).symm
  let f := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ rectangularCoordinates Φ
  have hFactor : euclideanHaarFactor a P = euclideanHaarFactor a V := by
    simp only [euclideanHaarFactor, J.toLinearEquiv.finrank_eq]
  have hf : (partitionedSchwartz p Φ : P → ℂ) = (f : V → ℂ) ∘ J := rfl
  change scaledEuclideanFourier a (partitionedSchwartz p Φ) z = scaledEuclideanFourier a f (J z)
  rw [scaledEuclideanFourier_apply, scaledEuclideanFourier_apply, hFactor,
    SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_coe, hf,
    Real.fourierInv_comp_linearIsometry, map_smul]

private theorem inner_entry_coordinates {ι : Type u} [Fintype ι] (x z : ι → ℝ) :
    inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) = ∑ i, x i * z i := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm (z i) (x i)

private theorem realRectangularSlices (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (x₀ : A → ℝ) (y₀ : B → ℝ) :
    let μA := Measure.pi fun _ : A => (realSelfDualMeasure a).measure
    let μB := Measure.pi fun _ : B => (realSelfDualMeasure a).measure
    let f := fun x : A → ℝ => Φ (joinRectangularCoordinates p x y₀) *
      (realScaledCharacter a).complex (∑ i, x i * x₀ i)
    let g := fun y : B → ℝ => realRectangularSchwartzFourier a Φ (joinRectangularCoordinates p x₀ y) *
      (realScaledCharacter a).complex (-(∑ i, y i * y₀ i))
    Integrable f μA ∧ Integrable g μB ∧ (∫ y, g y ∂μB) = ∫ x, f x ∂μA := by
  dsimp only
  let Ψ := partitionedSchwartz p Φ
  obtain ⟨hL, hR, hEq⟩ := realGodementScaledProductFourier E F a Ψ
    (WithLp.toLp 2 x₀) (WithLp.toLp 2 y₀)
  let f := fun x : E => realScaledCharacter a (inner ℝ x (WithLp.toLp 2 x₀)) •
    Ψ (WithLp.toLp 2 (x, WithLp.toLp 2 y₀))
  let g := fun y : F => realScaledCharacter a (-(inner ℝ y (WithLp.toLp 2 y₀))) •
    scaledEuclideanFourier a Ψ (WithLp.toLp 2 (WithLp.toLp 2 x₀, y))
  have hf (x : A → ℝ) : f (WithLp.toLp 2 x) = Φ (joinRectangularCoordinates p x y₀) *
      (realScaledCharacter a).complex (∑ i, x i * x₀ i) := by
    simp only [f, inner_entry_coordinates]
    change realScaledCharacter a (∑ i, x i * x₀ i) •
      Φ (rectangularCoordinates ((partitionCoordinates p).symm
        (WithLp.toLp 2 (WithLp.toLp 2 x, WithLp.toLp 2 y₀)))) = _
    rw [assemble_partitionCoordinates]
    exact mul_comm _ _
  have hg (y : B → ℝ) : g (WithLp.toLp 2 y) =
      realRectangularSchwartzFourier a Φ (joinRectangularCoordinates p x₀ y) *
        (realScaledCharacter a).complex (-(∑ i, y i * y₀ i)) := by
    simp only [g, Ψ, inner_entry_coordinates, scaledEuclideanFourier_partition,
      assemble_partitionCoordinates]
    exact mul_comm _ _
  have hA := measurePreserving_toEuclidean a A
  have hB := measurePreserving_toEuclidean a B
  refine ⟨?_, ?_, ?_⟩
  · exact (hA.integrable_comp_of_integrable (show Integrable f _ from hL)).congr
      (Filter.Eventually.of_forall hf)
  · exact (hB.integrable_comp_of_integrable (show Integrable g _ from hR)).congr
      (Filter.Eventually.of_forall hg)
  · calc
      _ = ∫ y : B → ℝ, g (WithLp.toLp 2 y) ∂Measure.pi (fun _ => (realSelfDualMeasure a).measure) :=
        (integral_congr_ae (Filter.Eventually.of_forall hg)).symm
      _ = ∫ y : F, g y ∂euclideanSelfDualMeasure a F := hB.integral_comp' g
      _ = ∫ x : E, f x ∂euclideanSelfDualMeasure a E := hEq
      _ = ∫ x : A → ℝ, f (WithLp.toLp 2 x) ∂Measure.pi (fun _ => (realSelfDualMeasure a).measure) :=
        (hA.integral_comp' f).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall hf)

end Partition

/-- For any partition of the entries, complementary affine slices of a real
Schwartz function and its full positive transform satisfy Fourier inversion. -/
def RealGodementRectangularFourierStatement : Prop :=
  ∀ (r s : ℕ) (p : Fin r × Fin s → Prop) [DecidablePred p]
    (a : ℝˣ) (Φ : 𝓢(Matrix (Fin r) (Fin s) ℝ, ℂ))
    (x₀ : {q // p q} → ℝ) (y₀ : {q // ¬p q} → ℝ),
    let μA := Measure.pi fun _ : {q // p q} => (realSelfDualMeasure a).measure
    let μB := Measure.pi fun _ : {q // ¬p q} => (realSelfDualMeasure a).measure
    let f := fun x : {q // p q} → ℝ => Φ (joinRectangularCoordinates p x y₀) *
      (realScaledCharacter a).complex (∑ i, x i * x₀ i)
    let g := fun y : {q // ¬p q} → ℝ => realRectangularSchwartzFourier a Φ
      (joinRectangularCoordinates p x₀ y) * (realScaledCharacter a).complex (-(∑ i, y i * y₀ i))
    Integrable f μA ∧ Integrable g μB ∧ (∫ y, g y ∂μB) = ∫ x, f x ∂μA

theorem realGodementRectangularFourier : RealGodementRectangularFourierStatement := by
  intro r s p _ a Φ x₀ y₀
  exact realRectangularSlices p a Φ x₀ y₀

end Langlands.Global.RankinSelbergGlobal.RealGodement
