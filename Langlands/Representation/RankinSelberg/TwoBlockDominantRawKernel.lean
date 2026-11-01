import Langlands.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData
import Langlands.Representation.RankinSelberg.TwoBlockDominantCovarianceData

/-!
# Raw scalar data for JPSS Section 4.10

The coefficient and determinant weight are evaluated on actual representatives.
The final rectangle covariance is specialized to the constructed matrix and residual
unipotent from `TwoBlockDominantCovarianceData`.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockLowerUnipotentQuotient TwoBlockLowerUnfolding

universe uF uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {t r j k : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : letI := F.canonicalTopologicalData.topology
  UnitaryAdditiveCharacter F.Carrier}
variable (ell : letI := F.canonicalTopologicalData.topology
  ∀ i, glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable (Wtest : letI := F.canonicalTopologicalData.topology
  WhittakerFunctions ψ r)

/-- The actual scalar section and test coefficient, before choosing the large-group
matrix argument. -/
def rawScalarValue (g : GeneralLinear (t + 1) F.Carrier)
    (P : GeneralLinear (r + 1) F.Carrier) : ℂ :=
  scalarSection (fun i => (ell i).val) f g 1 * Wtest.val P

/-- The determinant weight on a lower-unipotent translate is unchanged for any complex
exponent. This uses the determinant-one law of the actual lower subgroup. -/
theorem determinantWeight_lowerBlockUnipotent_mul (z : ℂ)
    (u : lowerBlockUnipotent h F.Carrier) (g : GeneralLinear (t + 1) F.Carrier) :
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) (u.val * g) z =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g z := by
  have hd : Matrix.det u.val.val = 1 := by
    simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using
      congrArg (fun a : F.Carrierˣ => (a : F.Carrier))
        (determinant_eq_one_of_mem_lowerBlockUnipotent h F.Carrier u.property)
  simp only [determinantWeight, Units.val_mul, Matrix.det_mul, hd, one_mul]

/-- Algebraic cancellation at actual matrix arguments. The later rectangle theorem supplies
`v` and its character law from the residual-unipotent construction. -/
private theorem rawScalarValue_cancel
    (u : lowerBlockUnipotent h F.Carrier) (v : upperUnipotent (r + 1) F.Carrier)
    (hv : letI := F.canonicalTopologicalData.topology
      standardCharacter ψ r v =
        ∏ i, standardCharacter ψ (m i) (diagonalBlocks h F.Carrier u i))
    (g : GeneralLinear (t + 1) F.Carrier) (P : GeneralLinear (r + 1) F.Carrier) :
    rawScalarValue ell f Wtest (u.val * g) (v.val * P) =
      rawScalarValue ell f Wtest g P := by
  let := F.canonicalTopologicalData.topology
  have h0 : (standardCharacter ψ (m 0) (diagonalBlocks h F.Carrier u 0) : ℂ) *
      (inverseStandardCharacter ψ (m 0) (diagonalBlocks h F.Carrier u 0) : ℂ) = 1 :=
    Units.mul_inv _
  have h1 : (standardCharacter ψ (m 1) (diagonalBlocks h F.Carrier u 1) : ℂ) *
      (inverseStandardCharacter ψ (m 1) (diagonalBlocks h F.Carrier u 1) : ℂ) = 1 :=
    Units.mul_inv _
  rw [rawScalarValue, rawScalarValue, scalarSection_lowerBlockUnipotent_mul ell f u g,
    Wtest.property v P, hv, Fin.prod_univ_two, Fin.prod_univ_two, Units.val_mul]
  calc _ =
      ((standardCharacter ψ (m 0) (diagonalBlocks h F.Carrier u 0) : ℂ) *
        (inverseStandardCharacter ψ (m 0) (diagonalBlocks h F.Carrier u 0) : ℂ)) *
      ((standardCharacter ψ (m 1) (diagonalBlocks h F.Carrier u 1) : ℂ) *
        (inverseStandardCharacter ψ (m 1) (diagonalBlocks h F.Carrier u 1) : ℂ)) *
      (scalarSection (fun i => (ell i).val) f g 1 * Wtest.val P) := by ring
    _ = _ := by rw [h0, h1, one_mul, one_mul]

/-- Cancellation for the computed residual, with its character supplied by the
constructed matrices rather than by a hypothesis on the caller. -/
private theorem rawScalarValue_residual
    (hr : r=t+(j+k+1)) (u : lowerBlockUnipotent h F.Carrier)
    (x : Matrix (Fin (m 0+1)) (Fin k) F.Carrier)
    (y : Matrix (Fin j) (Fin (m 1+1)) F.Carrier)
    (g : GeneralLinear (t+1) F.Carrier) (P : GeneralLinear (r+1) F.Carrier) :
    rawScalarValue ell f Wtest (u.val * g) ((residualUnipotent h hr u x y).val * P) =
      rawScalarValue ell f Wtest g P := by
  apply rawScalarValue_cancel
  let := F.canonicalTopologicalData.topology
  simpa only [Fin.prod_univ_two] using residualUnipotent_character h hr u x y ψ

/-- The unweighted scalar kernel at the actual Section 4.10 matrix. -/
def rawKernel (hr : r=t+(j+k+1)) (g : GeneralLinear (t+1) F.Carrier)
    (x : Matrix (Fin (m 0+1)) (Fin k) F.Carrier)
    (y : Matrix (Fin j) (Fin (m 1+1)) F.Carrier) : ℂ :=
  rawScalarValue ell f Wtest g (matrix h hr g x y)

/-- The representative-level kernel of Section 4.10(2), with its actual determinant
weight and with all inverse block Whittaker functionals, including zero. -/
def kernel (hr : r=t+(j+k+1)) (s : ℂ) (g : GeneralLinear (t+1) F.Carrier)
    (x : Matrix (Fin (m 0+1)) (Fin k) F.Carrier)
    (y : Matrix (Fin j) (Fin (m 1+1)) F.Carrier) : ℂ :=
  rawKernel ell f Wtest hr g x y *
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
      (s - ((j+k+1 : ℕ) : ℂ)/2 + (j : ℂ))

/-- Evaluation of the kernel on the actual section, coefficient and matrix. -/
theorem kernel_eq (hr : r=t+(j+k+1)) (s : ℂ) (g : GeneralLinear (t+1) F.Carrier)
    (x : Matrix (Fin (m 0+1)) (Fin k) F.Carrier)
    (y : Matrix (Fin j) (Fin (m 1+1)) F.Carrier) :
    kernel ell f Wtest hr s g x y =
      scalarSection (fun i => (ell i).val) f g 1 * Wtest.val (matrix h hr g x y) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
          (s - ((j+k+1 : ℕ) : ℂ)/2 + (j : ℂ)) := rfl

/-- The actual unweighted kernel is covariant under the simultaneous rectangle
change computed from the lower-group element. -/
theorem rawKernel_covariance (hr : r=t+(j+k+1))
    (u : lowerBlockUnipotent h F.Carrier) (g : GeneralLinear (t+1) F.Carrier)
    (x : Matrix (Fin (m 0+1)) (Fin k) F.Carrier)
    (y : Matrix (Fin j) (Fin (m 1+1)) F.Carrier) :
    rawKernel ell f Wtest hr (u.val * g) x y =
      rawKernel ell f Wtest hr g
        ((rectangleChange h j k u (x,y)).1) ((rectangleChange h j k u (x,y)).2) := by
  unfold rawKernel
  rw [matrix_covariance h hr u g x y]
  exact rawScalarValue_residual ell f Wtest hr u x y g _

/-- The weighted representative kernel has the same actual rectangle covariance
for every complex parameter, using determinant one of the lower-group element. -/
theorem kernel_covariance (hr : r=t+(j+k+1)) (s : ℂ)
    (u : lowerBlockUnipotent h F.Carrier) (g : GeneralLinear (t+1) F.Carrier)
    (x : Matrix (Fin (m 0+1)) (Fin k) F.Carrier)
    (y : Matrix (Fin j) (Fin (m 1+1)) F.Carrier) :
    kernel ell f Wtest hr s (u.val * g) x y =
      kernel ell f Wtest hr s g
        ((rectangleChange h j k u (x,y)).1) ((rectangleChange h j k u (x,y)).2) := by
  unfold kernel
  rw [rawKernel_covariance ell f Wtest hr u g x y,
    determinantWeight_lowerBlockUnipotent_mul]

end Langlands.RankinSelberg.TwoBlockDominantRectangular
