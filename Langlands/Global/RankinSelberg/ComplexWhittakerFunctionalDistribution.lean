import Langlands.Global.RankinSelberg.ComplexBorelProfileBound
import Langlands.Global.RankinSelberg.ComplexWhittakerTranslateExtension
import Langlands.Representation.Archimedean.WhittakerRootCovariance

/-! # Distributions from smooth complex standard-module functionals -/

noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open ComplexCompactSmoothDifferences (CompactProfileDifferenceBound)
open ComplexWhittakerSmoothExtension (compactProfile)
open ComplexWhittakerTranslateExtension (smoothTranslate smoothTranslate_apply)

variable (n : ℕ) (ds : List ComplexCharacterData)

local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "GL" => Langlands.GeneralLinear n ℂ
local notation "Std" => complexStandardModule n ds
local notation "Ω" => matrixUnitsOpen ℂ n
local notation "Test" => 𝓓(Ω, ℂ)

variable [SecondCountableTopology (upperTriangularSubgroup n ℂ)]
  [MeasurableSpace (upperTriangularSubgroup n ℂ)] [BorelSpace (upperTriangularSubgroup n ℂ)]
  (μ : Measure (upperTriangularSubgroup n ℂ)) [μ.IsHaarMeasure]

/-- Compose a smooth section functional of finite compact difference order
with the Borel test map, as an actual continuous linear distribution. -/
def complexBorelFunctionalDistribution
    (L : Std →ₗ[ℂ] ℂ) (J : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ F D, CompactProfileDifferenceBound J (compactProfile F) D → ‖L F‖ ≤ C * D) :
    Test →L[ℂ] ℂ := by
  let B := complexStandardBorelTestMap n ds μ
  let T := L.comp B
  refine TestFunction.mkCLM ℂ T (map_add T) (map_smul T) (fun K hK => ?_)
  obtain ⟨A, hA, hBound⟩ := complexBorelProfileBound n μ ds J K hK
  let TK := T.comp (TestFunction.ofSupportedInCLM ℂ hK).toLinearMap
  change Continuous TK
  apply WithSeminorms.continuous_normedSpace_rng ℂ
    (ContDiffMapSupportedIn.withSeminorms ℂ Mat ℂ ⊤ K)
  refine ⟨Finset.Iic J, ⟨C * A, mul_nonneg hC hA⟩, fun f => ?_⟩
  let F := B (TestFunction.ofSupportedIn hK f)
  let D := ContDiffMapSupportedIn.supSeminorm ℂ Mat ℂ ⊤ K J f
  change ‖L F‖ ≤ (C * A) * D
  rw [mul_assoc]
  exact hL F (A * D) (hBound f)

@[simp]
theorem complexBorelFunctionalDistribution_apply (L : Std →ₗ[ℂ] ℂ) (J : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ F D, CompactProfileDifferenceBound J (compactProfile F) D → ‖L F‖ ≤ C * D)
    (f : Test) :
    complexBorelFunctionalDistribution n ds μ L J C hC hL f =
      L (complexStandardBorelTestMap n ds μ f) :=
  rfl

theorem complexBorelFunctionalDistribution_injective
    (L₀ L₁ : Std →ₗ[ℂ] ℂ) (J₀ J₁ : ℕ) (C₀ C₁ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hL₀ : ∀ F D, CompactProfileDifferenceBound J₀ (compactProfile F) D → ‖L₀ F‖ ≤ C₀ * D)
    (hL₁ : ∀ F D, CompactProfileDifferenceBound J₁ (compactProfile F) D → ‖L₁ F‖ ≤ C₁ * D)
    (z : ℂ)
    (h : ∀ f, complexBorelFunctionalDistribution n ds μ L₁ J₁ C₁ hC₁ hL₁ f =
      z * complexBorelFunctionalDistribution n ds μ L₀ J₀ C₀ hC₀ hL₀ f) :
    L₁ = z • L₀ := by
  apply LinearMap.ext
  intro F
  obtain ⟨f, rfl⟩ := complexStandardBorelTestMap_surjective n ds μ F
  exact h f

/-- A left translate of the matrix test becomes the inverse right translate
of the averaged standard section. -/
theorem complexStandardBorelTestMap_leftTranslate (u : GL) (f : Test) :
    complexStandardBorelTestMap n ds μ (matrixLeftTranslateTest u f) =
      smoothTranslate u⁻¹ (complexStandardBorelTestMap n ds μ f) := by
  apply Subtype.ext
  funext g
  simp only [complexStandardBorelTestMap_apply, smoothTranslate_apply,
    complexBorelMatrixAverage, matrixLeftTranslateTest_apply, mul_inv_rev, inv_inv,
    Units.val_mul, mul_assoc]

end Langlands.Global.RankinSelbergGlobal
