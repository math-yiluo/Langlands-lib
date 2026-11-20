import Langlands.Representation.GodementJacquet.ComplexJacquetRectangleCoordinates
import Langlands.Representation.GodementJacquet.ComplexRectangularFourierCovariance
import Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement

/-! # The unipotent and last-column average in the complex Jacquet recursion -/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.Global.RankinSelbergGlobal
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "I" => Fin m
local notation "U" => upperUnipotent m ℂ
local notation "Z" => I → ℂ
local notation "R" => Matrix I (Fin (m + 1)) ℂ

/-- The two iterated integrals over the upper-unipotent entries and the last
column, with their common character parameter. -/
def complexJacquetUnipotentAverage (a : ℂˣ) (μ : Measure U) (f : R → ℂ) : ℂ :=
  ∫ u, ∫ z, complexJacquetRectangleKernel a f (u, z) ∂complexCoordinateMeasure I a ∂μ

theorem complexJacquetUnipotentAverage_const_mul (a : ℂˣ) (μ : Measure U)
    (c : ℂ) (f : R → ℂ) :
    complexJacquetUnipotentAverage a μ (fun X => c * f X) =
      c * complexJacquetUnipotentAverage a μ f := by
  simp only [complexJacquetUnipotentAverage, complexJacquetRectangleKernel, mul_assoc, integral_const_mul]

/-- The Fourier identity between the reversed rectangular tests in average form. -/
theorem complexJacquetUnipotentAverage_weyl (a : ℂˣ) (μ : Measure U) [μ.IsHaarMeasure]
    (Φ : SchwartzMap R ℂ) :
    complexJacquetUnipotentAverage (-a) μ (fun X => Φ (X * (weylLong (m + 1) ℂ).val)) =
      complexJacquetUnipotentAverage a μ
        (fun X => complexRectangularFourier (-a) Φ ((weylLong m ℂ).val * X)) := by
  have h := (integral_complexJacquetRectangle_unipotent a Φ μ).2.2
  simpa only [complexJacquetUnipotentAverage, complexRectangularFourier,
    complexCoordinateMeasure, complexSelfDualMeasure_neg_scale] using h

private theorem rectangularJoin_unipotentMul (u v : U) (z : Z) :
    rectangularJoin (u * v).val.val (u.val.val.mulVec z) =
      u.val.val * rectangularJoin v.val.val z :=
  rectangularJoin_left_mul u.val.val v.val.val z

private theorem unipotent_mulVec_last (u : U) (z : Z) :
    u.val.val.mulVec z (Fin.last r) = z (Fin.last r) := by
  classical
  unfold Matrix.mulVec dotProduct
  change (∑ i, u.val.val (Fin.last r) i * z i) = _
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [u.property.2 (Fin.last r), one_mul]
  · intro i _ hi
    have hz : u.val.val (Fin.last r) i = 0 :=
      u.property.1 (lt_of_le_of_ne (Fin.le_last i) hi)
    rw [hz, zero_mul]
  · simp

private theorem unipotentFourierSum_mul (u v : U) :
    unipotentFourierSum r (u * v) = unipotentFourierSum r u + unipotentFourierSum r v := by
  simp only [unipotentFourierSum, UpperUnipotent.mul_adjacent_entry, Finset.sum_add_distrib]

private theorem measurePreserving_unipotentColumnMul (a : ℂˣ) (u : U) :
    MeasurePreserving (complexColumnMul u.val) (complexCoordinateMeasure I a)
      (complexCoordinateMeasure I a) := by
  refine ⟨(complexColumnMul u.val).continuous.measurable, ?_⟩
  rw [map_complexColumnMul, RankinSelberg.unipotent_det, map_one, inv_one, one_smul]

/-- Left translation of the rectangular test by an upper-unipotent matrix
extracts its inverse character from the average. -/
theorem complexJacquetUnipotentAverage_unipotent (a : ℂˣ) (μ : Measure U) [μ.IsHaarMeasure]
    (f : R → ℂ) (v : U) :
    complexJacquetUnipotentAverage a μ (fun X => f (v.val.val * X)) =
      traceCharacter a (-unipotentFourierSum r v) * complexJacquetUnipotentAverage a μ f := by
  let ν := complexCoordinateMeasure I a
  let F := complexJacquetRectangleKernel a f
  have hkernel (u : U) (z : Z) :
      complexJacquetRectangleKernel a (fun X => f (v.val.val * X)) (u, z) =
        traceCharacter a (-unipotentFourierSum r v) * F (v * u, complexColumnMul v.val z) := by
    simp only [F, complexJacquetRectangleKernel, complexColumnMul_apply,
      rectangularJoin_unipotentMul, unipotent_mulVec_last, unipotentFourierSum_mul]
    have he : z (Fin.last r) + unipotentFourierSum r u =
        -unipotentFourierSum r v + (z (Fin.last r) +
          (unipotentFourierSum r v + unipotentFourierSum r u)) := by abel
    rw [he, traceCharacter_add]
    ring
  have hcol (u : U) :
      (∫ z, F (v * u, complexColumnMul v.val z) ∂ν) = ∫ z, F (v * u, z) ∂ν :=
    (measurePreserving_unipotentColumnMul a v).integral_comp
      (complexColumnMul v.val).toHomeomorph.measurableEmbedding (fun z => F (v * u, z))
  simp only [complexJacquetUnipotentAverage, hkernel, integral_const_mul, hcol, ν, F]
  rw [integral_mul_left_eq_self (fun u : U => ∫ z, F (u, z) ∂ν) v]

end Langlands.GodementJacquet
