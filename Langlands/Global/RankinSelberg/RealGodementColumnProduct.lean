import Langlands.Global.RankinSelberg.ComplexGodementColumnProduct
import Langlands.Global.RankinSelberg.RealAdjacentGodementRestriction
import Langlands.Global.RankinSelberg.RealGodementRowFourierInversion

/-! # Real rectangular Fourier transform of a separated last-column test -/

noncomputable section

open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (rectangularMeasure)
open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal RealGodement

variable {r : ℕ}
local notation "m" => (r + 1)
local notation "R" => (Fin (r + 1) → ℝ)
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "X" => Matrix (Fin (r + 1)) (Fin (r + 2)) ℝ

/-- The square block of leading columns of the rectangle. -/
def leadingColumns (B : X) : M := B.submatrix id Fin.castSucc

/-- The trailing column of the rectangle. -/
def lastColumn (B : X) : R := fun i => B i (Fin.last m)

@[simp] theorem leadingColumns_joinLastColumn (A : M) (x : R) :
    leadingColumns (joinLastColumn A x) = A := by
  ext i j
  simp [leadingColumns, joinLastColumn]

@[simp] theorem lastColumn_joinLastColumn (A : M) (x : R) :
    lastColumn (joinLastColumn A x) = x := by
  funext i
  simp [lastColumn, joinLastColumn]

@[simp] theorem joinLastColumn_leadingColumns_lastColumn (B : X) :
    joinLastColumn (leadingColumns B) (lastColumn B) = B := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [leadingColumns, lastColumn, joinLastColumn]

private def leadingColumnsCLM : X →L[ℝ] M :=
  LinearMap.toContinuousLinearMap
    { toFun := leadingColumns, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

private def lastColumnCLM : X →L[ℝ] R :=
  LinearMap.toContinuousLinearMap
    { toFun := lastColumn, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

private def leadingJoinCLM : M →L[ℝ] X :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => joinLastColumn A 0
      map_add' := fun A B => by
        ext i j
        refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [joinLastColumn]
      map_smul' := fun c A => by
        ext i j
        refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [joinLastColumn] }

private def lastJoinCLM : R →L[ℝ] X :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => joinLastColumn 0 x
      map_add' := fun x y => by
        ext i j
        refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [joinLastColumn]
      map_smul' := fun c x => by
        ext i j
        refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [joinLastColumn] }

private theorem norm_le_columnSplit (B : X) :
    ‖B‖ ≤ (‖leadingJoinCLM (r := r)‖ + ‖lastJoinCLM (r := r)‖) *
      (‖leadingColumnsCLM B‖ + ‖lastColumnCLM B‖) := by
  have hB : leadingJoinCLM (leadingColumnsCLM B) + lastJoinCLM (lastColumnCLM B) = B := by
    ext i j
    change (joinLastColumn (leadingColumns B) 0 + joinLastColumn 0 (lastColumn B)) i j = B i j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [joinLastColumn, leadingColumns, lastColumn]
  have h₁ := (leadingJoinCLM (r := r)).le_opNorm (leadingColumnsCLM B)
  have h₂ := (lastJoinCLM (r := r)).le_opNorm (lastColumnCLM B)
  calc
    ‖B‖ = ‖leadingJoinCLM (leadingColumnsCLM B) + lastJoinCLM (lastColumnCLM B)‖ := by rw [hB]
    _ ≤ ‖leadingJoinCLM (leadingColumnsCLM B)‖ + ‖lastJoinCLM (lastColumnCLM B)‖ := norm_add_le _ _
    _ ≤ _ := by
      have h₃ := mul_nonneg (norm_nonneg (leadingJoinCLM (r := r))) (norm_nonneg (lastColumnCLM B))
      have h₄ := mul_nonneg (norm_nonneg (lastJoinCLM (r := r))) (norm_nonneg (leadingColumnsCLM B))
      nlinarith only [h₁, h₂, h₃, h₄]

/-- The real Schwartz rectangle test `B ↦ F(leading columns) f(last column)`. -/
def realColumnProduct (F : 𝓢(M, ℂ)) (f : 𝓢(R, ℂ)) : 𝓢(X, ℂ) :=
  ComplexGodementColumnProduct.schwartzProd leadingColumnsCLM lastColumnCLM
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) norm_le_columnSplit F f

@[simp] theorem realColumnProduct_apply (F : 𝓢(M, ℂ)) (f : 𝓢(R, ℂ)) (B : X) :
    realColumnProduct F f B = F (leadingColumns B) * f (lastColumn B) := rfl

private def columnSplitEquiv : X ≃ᵐ R × M :=
  (MeasurableEquiv.piCongrRight fun _ : Fin m =>
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 2) => ℝ) (Fin.last m)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ (Fin m → ℝ) (Fin m))

private theorem columnSplitEquiv_apply (B : X) :
    columnSplitEquiv B = (lastColumn B, leadingColumns B) := by
  refine Prod.ext rfl ?_
  ext i j
  change B i ((Fin.last m).succAbove j) = B i j.castSucc
  rw [Fin.succAbove_last]

private theorem measurePreserving_columnSplitEquiv (ν : Measure ℝ) [SigmaFinite ν] :
    MeasurePreserving (columnSplitEquiv (r := r))
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (r + 2) => ν)
      ((Measure.pi fun _ : Fin m => ν).prod
        (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin m => ν)) :=
  (measurePreserving_arrowProdEquivProdArrow ℝ (Fin m → ℝ) (Fin m) (fun _ => ν)
      (fun _ => Measure.pi fun _ : Fin m => ν)).comp
    (measurePreserving_pi _ _ fun _ =>
      measurePreserving_piFinSuccAbove (fun _ : Fin (r + 2) => ν) (Fin.last m))

private theorem rectangularPairing_eq_add (Y Z : X) :
    rectangularPairing Y Z = (∑ i, lastColumn Y i * lastColumn Z i) +
      rectangularPairing (leadingColumns Y) (leadingColumns Z) := by
  simp only [rectangularPairing, Fin.sum_univ_castSucc, Finset.sum_add_distrib, lastColumn,
    leadingColumns, Matrix.submatrix_apply, id]
  ring

private theorem rectangularFourierIntegral_column_mul (a : ℝˣ) (F : M → ℂ) (f : R → ℂ) (Z : X) :
    rectangularFourierIntegral (realScaledCharacter a) (realSelfDualMeasure a)
      (fun Y => F (leadingColumns Y) * f (lastColumn Y)) Z =
    rectangularFourierIntegral (realScaledCharacter a) (realSelfDualMeasure a) F (leadingColumns Z) *
      realFourierTransform a f (lastColumn Z) := by
  let ψ := (realScaledCharacter a).complex
  let μ := realSelfDualMeasure a
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let g : R × M → ℂ := fun p =>
    (f p.1 * ψ (∑ i, p.1 i * lastColumn Z i)) *
      (F p.2 * ψ (rectangularPairing p.2 (leadingColumns Z)))
  calc
    _ = ∫ Y, g (columnSplitEquiv Y) ∂rectangularMeasure μ m (r + 2) := by
      unfold rectangularFourierIntegral
      exact integral_congr_ae (ae_of_all _ fun Y => by
        change F (leadingColumns Y) * f (lastColumn Y) * ψ (rectangularPairing Y Z) = _
        simp only [g, columnSplitEquiv_apply, rectangularPairing_eq_add, AddChar.map_add_eq_mul]
        ring)
    _ = ∫ p, g p ∂(Measure.pi fun _ : Fin m => μ.measure).prod (rectangularMeasure μ m m) :=
      (measurePreserving_columnSplitEquiv μ.measure).integral_comp' g
    _ = (∫ v, f v * ψ (∑ i, v i * lastColumn Z i) ∂Measure.pi fun _ : Fin m => μ.measure) *
        rectangularFourierIntegral (realScaledCharacter a) (realSelfDualMeasure a) F (leadingColumns Z) :=
      integral_prod_mul (fun v : R => f v * ψ (∑ i, v i * lastColumn Z i))
        (fun S : M => F S * ψ (rectangularPairing S (leadingColumns Z)))
    _ = _ := mul_comm _ _

/-- Full positive Fourier transformation preserves the separated column product, with the
actual square and row self-dual transforms of the two factors. -/
theorem realColumnProduct_fourier (a : ℝˣ) (F : 𝓢(M, ℂ)) (f : 𝓢(R, ℂ)) :
    realRectangularSchwartzFourier a (realColumnProduct F f) =
      realColumnProduct (realRectangularSchwartzFourier a F) (realRowSchwartzFourier m a f) := by
  ext Z
  rw [realRectangularSchwartzFourier_apply, realColumnProduct_apply, realRectangularSchwartzFourier_apply,
    realRowSchwartzFourier_apply]
  exact rectangularFourierIntegral_column_mul a F f Z

end Langlands.Global.RankinSelbergGlobal.RealJacquet
