import Langlands.Global.RankinSelberg.ComplexAdjacentSplitFourier
import Langlands.Global.RankinSelberg.ComplexUnequalJacquetConventionReduction

/-! # The finite products in the unfolded complex adjacent-rank integral -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open ArchimedeanLocal (ComplexQuotientMeasureData complexNormalizedAbs
  complexSelfDualMeasure complexFourierTransform complexEqualIntegrand complexEqualIntegral)
open Langlands.GeneralLinear Langlands.GodementJacquet Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ComplexGodement (characterWeight)
open ComplexSquareFourier (matrixTransform matrixTransform_apply)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Vec" => Fin (r + 1) → ℂ

/-- The positive square transform uses the square equation at the opposite parameter. -/
theorem splitSquareTransform_eq_matrixTransform_neg (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) :
    splitSquareTransform a Φ = matrixTransform (-a) Φ := by
  ext X
  rw [splitSquareTransform_apply, matrixTransform_apply, matrixTransform_apply,
    complexSelfDualMeasure_neg_scale]
  refine integral_congr_ae (ae_of_all _ fun (Y : Mat) => ?_)
  have hs : -Matrix.trace (Matrix.transpose (-X) * Y) =
      -(-Matrix.trace (Matrix.transpose X * Y)) := by
    simp only [Matrix.transpose_neg, neg_mul, Matrix.trace_neg]
  have h := traceCharacter_neg_scale a (-Matrix.trace (Matrix.transpose X * Y))
  exact congrArg (Φ Y * ·) (by simpa only [hs] using h.symm)

/-- The row test in the opposite-parameter smaller equal-rank equation is the original column test. -/
theorem complexFourierTransform_splitRowTransform (a : ℂˣ) (φ : 𝓢(Vec, ℂ)) (y : Vec) :
    complexFourierTransform (-a) (splitRowTransform a φ) y = φ y := by
  rw [← (complexAdjacentSplitFourier a (0 : 𝓢(Mat, ℂ)) φ).2 y]
  unfold complexFourierTransform ArchimedeanLocal.fourierTransform splitRowPlus
  rw [complexSelfDualMeasure_neg_scale]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  exact congrArg (fun x => splitRowTransform a φ v * (complexScaledCharacter (-a)).complex x)
    (Finset.sum_congr rfl fun i _ => mul_comm (v i) (y i))

/-- A finite coefficient expansion of the averaged Whittaker factor separates the
absolutely integrable unfolded product into smaller equal and square integrals. -/
def ComplexAdjacentProductExpansionStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure] (ν : Measure G) [SFinite ν]
    (d : ComplexCharacterData) (p s : ℂ) (Φ : Mat → ℂ) (φ : Vec → ℂ)
    (U : G → ℂ) (m : ℕ) (W C : Fin m → G → ℂ) (V : G → G → ℂ),
    (∀ x z, V x z = ∑ j, W j x * C j z) →
    let P := fun z : G => Φ z.val * characterWeight d (p + s) (determinant z)
    (∀ j, Integrable (fun z => P z * C j z) ν) →
    (∀ j, Integrable (complexEqualIntegrand U (W j) φ s) D.measure) →
    (∫ x : G × Q, P x.1 *
      ArchimedeanLocal.equalIntegrand complexNormalizedAbs U (fun g => V g x.1) φ s x.2 ∂ν.prod D.measure) =
      ∑ j, complexEqualIntegral D U (W j) φ s * ∫ z, P z * C j z ∂ν

theorem complexAdjacentProductExpansion : ComplexAdjacentProductExpansionStatement (r := r) := by
  intro D _ ν _ d p s Φ φ U m W C V hV P hC hW
  let Z (j : Fin m) (z : G) := P z * C j z
  let E (j : Fin m) (q : Q) := complexEqualIntegrand U (W j) φ s q
  have hpoint (x : G × Q) : P x.1 *
      ArchimedeanLocal.equalIntegrand complexNormalizedAbs U (fun g => V g x.1) φ s x.2 =
        ∑ j, Z j x.1 * E j x.2 := by
    simp only [Z, E, complexEqualIntegrand, ArchimedeanLocal.equalIntegrand, hV, Finset.sum_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun j _ => (hC j).mul_prod (hW j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  change (∫ x : G × Q, Z j x.1 * E j x.2 ∂ν.prod D.measure) =
    (∫ q, E j q ∂D.measure) * ∫ z, Z j z ∂ν
  rw [integral_prod_mul (Z j) (E j)]
  exact mul_comm _ _

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
