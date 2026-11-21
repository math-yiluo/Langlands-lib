import Langlands.Global.RankinSelberg.RealGodementPartialFourier
import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Global.RankinSelberg.RectangleTateMeasure
import Langlands.HarmonicAnalysis.RowFourier
import Langlands.Representation.Archimedean.PartialJacquetIntegral

/-! # Fourier transformation in the free first Godement column -/

noncomputable section

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal Langlands.Archimedean
open MeasureTheory Matrix
open scoped Matrix.Norms.Operator SchwartzMap RealInnerProductSpace NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {m : ℕ}

local notation "V" => (Fin m → ℝ)
local notation "M" => Matrix (Fin m) (Fin m) ℝ
local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin m × Fin m)
local notation "P" => WithLp 2 (E × F)

/-- A rectangle with free first column and a square trailing block. -/
def joinFirstColumn (x : V) (A : M) : X := fun i j => Fin.cases (x i) (A i) j

@[simp] theorem joinFirstColumn_zero (x : V) (A : M) (i : Fin m) :
    joinFirstColumn x A i 0 = x i := rfl

@[simp] theorem joinFirstColumn_succ (x : V) (A : M) (i j : Fin m) :
    joinFirstColumn x A i j.succ = A i j := rfl

private def firstColumnCoordinates (m : ℕ) :
    WithLp 2 (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m × Fin m)) ≃L[ℝ]
      Matrix (Fin m) (Fin (m + 1)) ℝ :=
  ({ toFun := fun p => joinFirstColumn (fun i => p.fst i) (fun i j => p.snd (i, j))
     invFun := fun Y => WithLp.toLp 2 (WithLp.toLp 2 (fun i => Y i 0),
       WithLp.toLp 2 (fun ij => Y ij.1 ij.2.succ))
     left_inv := by
       intro p
       apply WithLp.ofLp_injective 2
       apply Prod.ext <;> apply WithLp.ofLp_injective 2
       · funext i
         rfl
       · funext ij
         rfl
     right_inv := by
       intro Y
       ext i j
       refine Fin.cases ?_ (fun j => ?_) j <;> rfl
     map_add' := by
       intro p q
       ext i j
       refine Fin.cases ?_ (fun j => ?_) j <;> rfl
     map_smul' := by
       intro c p
       ext i j
       refine Fin.cases ?_ (fun j => ?_) j <;> rfl } :
    WithLp 2 (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m × Fin m)) ≃ₗ[ℝ]
      Matrix (Fin m) (Fin (m + 1)) ℝ).toContinuousLinearEquiv

private def columnTest (Φ : 𝓢(X, ℂ)) : 𝓢(P, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (firstColumnCoordinates m) Φ

/-- Positive Fourier integral in the first column of a real rectangle. -/
def firstColumnFourier (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (ξ : V) (A : M) : ℂ :=
  scaledFirstFactorFourier a (columnTest Φ) (WithLp.toLp 2 ξ)
    (WithLp.toLp 2 (Function.uncurry A))

/-- The first-column Fourier integral at fixed slice coordinates is complex-linear in the test. -/
def firstColumnFourierLinear (a : ℝˣ) (ξ : V) (A : M) : 𝓢(X, ℂ) →ₗ[ℂ] ℂ := by
  let u : E := WithLp.toLp 2 ξ
  let v : F := WithLp.toLp 2 (Function.uncurry A)
  let f (Φ : 𝓢(X, ℂ)) (x : E) :=
    realScaledCharacter a (inner ℝ x u) • columnTest Φ (WithLp.toLp 2 (x, v))
  have hInt (Φ : 𝓢(X, ℂ)) := (realGodementScaledProductFourier E F a (columnTest Φ) u v).1
  refine { toFun := fun Φ => firstColumnFourier a Φ ξ A, map_add' := ?_, map_smul' := ?_ }
  · intro Φ Ψ
    change (∫ x, f (Φ + Ψ) x ∂euclideanSelfDualMeasure a E) =
      (∫ x, f Φ x ∂euclideanSelfDualMeasure a E) + ∫ x, f Ψ x ∂euclideanSelfDualMeasure a E
    have hAdd (x : E) : f (Φ + Ψ) x = f Φ x + f Ψ x := by
      simp only [f, columnTest, map_add, _root_.add_apply, smul_add]
    simp_rw [hAdd]
    exact integral_add (hInt Φ) (hInt Ψ)
  · intro c Φ
    change (∫ x, f (c • Φ) x ∂euclideanSelfDualMeasure a E) =
      c • ∫ x, f Φ x ∂euclideanSelfDualMeasure a E
    have hSmul (x : E) : f (c • Φ) x = c • f Φ x := by
      simp only [f, columnTest, map_smul, _root_.smul_apply, smul_comm c]
    simp_rw [hSmul]
    exact integral_smul c (f Φ)

@[simp] theorem firstColumnFourierLinear_apply (a : ℝˣ) (ξ : V) (A : M) (Φ : 𝓢(X, ℂ)) :
    firstColumnFourierLinear a ξ A Φ = firstColumnFourier a Φ ξ A := rfl

private theorem realColumnMeasure_eq (a : ℝˣ) :
    rowMeasure (realSelfDualMeasure a) m = ENNReal.ofReal (euclideanHaarFactor a E) • volume := by
  let c : ℝ≥0 := NNReal.sqrt ‖(a : ℝ)‖₊
  have hc : (c : ℝ) = Real.sqrt |(a : ℝ)| := by
    dsimp only [c]
    rw [Real.coe_sqrt, coe_nnnorm, Real.norm_eq_abs]
  change Measure.pi (fun _ : Fin m => c • (volume : Measure ℝ)) = _
  rw [RectangleTate.pi_smul_eq]
  congr 1
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, euclideanHaarFactor,
    finrank_euclideanSpace]
  rw [← hc, ← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow]

/-- Euclidean coordinates preserve the self-dual measure on a real column. -/
theorem measurePreserving_columnToEuclidean (a : ℝˣ) :
    MeasurePreserving (MeasurableEquiv.toLp 2 V) (rowMeasure (realSelfDualMeasure a) m)
      (euclideanSelfDualMeasure a E) := by
  have h := PiLp.volume_preserving_toLp (Fin m)
  refine ⟨h.measurable, ?_⟩
  rw [realColumnMeasure_eq, euclideanSelfDualMeasure]
  change Measure.map (WithLp.toLp 2) (_ • (volume : Measure V)) = _
  rw [Measure.map_smul _ h.measurable.aemeasurable, h.map_eq]

/-- The Euclidean partial transform is the integral in the original first-column
coordinates with the specified real self-dual measure. -/
theorem firstColumnFourier_apply (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (ξ : V) (A : M) :
    firstColumnFourier a Φ ξ A = ∫ x, Φ (joinFirstColumn x A) *
      (realScaledCharacter a).complex (x ⬝ᵥ ξ) ∂rowMeasure (realSelfDualMeasure a) m := by
  unfold firstColumnFourier scaledFirstFactorFourier
  let f : E → ℂ := fun x => realScaledCharacter a (inner ℝ x (WithLp.toLp 2 ξ)) •
    columnTest Φ (WithLp.toLp 2 (x, WithLp.toLp 2 (Function.uncurry A)))
  calc
    _ = ∫ x : V, f ((MeasurableEquiv.toLp 2 V) x) ∂rowMeasure (realSelfDualMeasure a) m :=
      ((measurePreserving_columnToEuclidean a).integral_comp' f).symm
    _ = _ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun x => ?_
      have hPair : inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 ξ) = x ⬝ᵥ ξ := by
        rw [PiLp.inner_apply, dotProduct]
        exact Finset.sum_congr rfl fun i _ => mul_comm (ξ i) (x i)
      change realScaledCharacter a (inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 ξ)) •
        Φ (joinFirstColumn x A) = _
      rw [hPair, Circle.smul_def, smul_eq_mul]
      change (realScaledCharacter a).complex (x ⬝ᵥ ξ) * Φ (joinFirstColumn x A) =
        Φ (joinFirstColumn x A) * (realScaledCharacter a).complex (x ⬝ᵥ ξ)
      exact mul_comm _ _

private theorem mul_joinFirstColumn (h A : M) (x : V) :
    h * joinFirstColumn x A = joinFirstColumn (h *ᵥ x) (h * A) := by
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, joinFirstColumn_zero]
  · simp only [Matrix.mul_apply, joinFirstColumn_succ]

private theorem column_dotProduct_inverseTranspose (h : Langlands.GeneralLinear m ℝ) (x ξ : V) :
    (h.val *ᵥ x) ⬝ᵥ ((inverseTranspose m ℝ h).val *ᵥ ξ) = x ⬝ᵥ ξ := by
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    inverseTranspose_coe, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.transpose_one, Matrix.one_mulVec]

private theorem integral_realColumn_mul (a : ℝˣ) (h : Langlands.GeneralLinear m ℝ) (f : V → ℂ) :
    (∫ x, f (h.val *ᵥ x) ∂rowMeasure (realSelfDualMeasure a) m) =
      ((|h.val.det|⁻¹ : ℝ) : ℂ) * ∫ x, f x ∂rowMeasure (realSelfDualMeasure a) m := by
  have hdet : h.val.transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact (determinant h).ne_zero
  simp only [realColumnMeasure_eq, integral_smul_measure, Complex.real_smul, ← Matrix.vecMul_transpose h.val]
  rw [PartialJacquet.integral_vecMul_eq hdet f, Matrix.det_transpose]
  ring

/-- Changing the free column by `h` gives the determinant Jacobian and the
inverse-transpose frequency in equation (7.7). -/
theorem firstColumnFourier_mul (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (h : Langlands.GeneralLinear m ℝ)
    (ξ : V) (A : M) :
    (∫ x, Φ (h.val * joinFirstColumn x A) *
      (realScaledCharacter a).complex (x ⬝ᵥ ξ) ∂rowMeasure (realSelfDualMeasure a) m) =
      ((|h.val.det|⁻¹ : ℝ) : ℂ) * firstColumnFourier a Φ ((inverseTranspose m ℝ h).val *ᵥ ξ) (h.val * A) := by
  rw [firstColumnFourier_apply]
  let f : V → ℂ := fun x => Φ (joinFirstColumn x (h.val * A)) *
    (realScaledCharacter a).complex (x ⬝ᵥ ((inverseTranspose m ℝ h).val *ᵥ ξ))
  calc
    _ = ∫ x, f (h.val *ᵥ x) ∂rowMeasure (realSelfDualMeasure a) m := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only [f]
        rw [mul_joinFirstColumn, column_dotProduct_inverseTranspose]
    _ = _ := integral_realColumn_mul a h f

/-- The real first-column transform has the required continuity, joint decay,
and normalized left-translation formula. -/
def RealGodementFirstColumnStatement : Prop :=
  ∀ (m : ℕ) (a : ℝˣ) (Φ : 𝓢(Matrix (Fin m) (Fin (m + 1)) ℝ, ℂ)),
    Continuous (fun p : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ => firstColumnFourier a Φ p.1 p.2) ∧
    (∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ξ : Fin m → ℝ) (A : Matrix (Fin m) (Fin m) ℝ),
      (1 + ‖(WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin m))‖) ^ N *
      (1 + ‖(WithLp.toLp 2 (Function.uncurry A) : EuclideanSpace ℝ (Fin m × Fin m))‖) ^ N *
        ‖firstColumnFourier a Φ ξ A‖ ≤ C) ∧
    ∀ (h : Langlands.GeneralLinear m ℝ) (ξ : Fin m → ℝ) (A : Matrix (Fin m) (Fin m) ℝ),
      (∫ x, Φ (h.val * joinFirstColumn x A) *
        (realScaledCharacter a).complex (x ⬝ᵥ ξ) ∂rowMeasure (realSelfDualMeasure a) m) =
        ((|h.val.det|⁻¹ : ℝ) : ℂ) * firstColumnFourier a Φ ((inverseTranspose m ℝ h).val *ᵥ ξ) (h.val * A)

private theorem firstColumnFourier_continuous (a : ℝˣ) (Φ : 𝓢(X, ℂ)) :
    Continuous (fun p : V × M => firstColumnFourier a Φ p.1 p.2) := by
  have hCont := (realGodementPartialFourier E F a (columnTest Φ)).1
  have hLeft : Continuous (fun p : V × M => (WithLp.toLp 2 p.1 : E)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp continuous_fst
  have hRight : Continuous (fun p : V × M => (WithLp.toLp 2 (Function.uncurry p.2) : F)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin m × Fin m => ℝ)).comp
    apply continuous_pi
    intro ij
    exact (continuous_apply ij.2).comp ((continuous_apply ij.1).comp continuous_snd)
  have h := hCont.comp (hLeft.prodMk hRight)
  exact h.congr (fun _ => rfl)

/-- The decay constant in first-column Fourier coordinates is a continuous
Schwartz seminorm of the original rectangular test. -/
theorem firstColumnFourier_decay_seminorm (a : ℝˣ) (N : ℕ) :
    ∃ q : Seminorm ℝ 𝓢(X, ℂ), Continuous q ∧ ∀ (Φ : 𝓢(X, ℂ)) (ξ : V) (A : M),
      (1 + ‖(WithLp.toLp 2 ξ : E)‖) ^ N *
      (1 + ‖(WithLp.toLp 2 (Function.uncurry A) : F)‖) ^ N *
        ‖firstColumnFourier a Φ ξ A‖ ≤ q Φ := by
  obtain ⟨q, hq, hBounds⟩ := scaledFirstFactorFourier_decay_seminorm («E» := E) («F» := F) a N
  let T := (SchwartzMap.compCLMOfContinuousLinearEquiv («F» := ℂ) ℂ
    (firstColumnCoordinates m)).restrictScalars ℝ
  exact ⟨q.comp T.toLinearMap, hq.comp T.continuous,
    fun Φ ξ A => hBounds (T Φ) (WithLp.toLp 2 ξ) (WithLp.toLp 2 (Function.uncurry A))⟩

theorem realGodementFirstColumn : RealGodementFirstColumnStatement := by
  intro m a Φ
  refine ⟨firstColumnFourier_continuous a Φ, ?_, firstColumnFourier_mul a Φ⟩
  intro N
  obtain ⟨q, _, hq⟩ := firstColumnFourier_decay_seminorm (m := m) a N
  exact ⟨q Φ, apply_nonneg _ _, hq Φ⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
