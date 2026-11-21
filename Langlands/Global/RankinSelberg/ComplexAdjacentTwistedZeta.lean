import Langlands.Global.RankinSelberg.ComplexSquareZetaCoefficientReflection
import Langlands.Representation.Archimedean.ComplexStandardDeterminantTwist
import Langlands.Representation.RankinSelberg.HighlyRamified.DualPointwise

/-! # The square equation for the determinant-twisted adjacent coefficients -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap NNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

open Langlands.Archimedean Langlands.Archimedean.ComplexDeterminantTwist
open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open ComplexSquareFourier (matrixTransform)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "K" => unitaryCompact ℂ (r + 1)
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "ι" => inverseTranspose (r + 1) ℂ

private theorem compactCoefficient_detMul (κ : Measure K) (d : ComplexCharacterData)
    (w : K → ℂ) (f : G → ℂ) (g : G) :
    compactCoefficient κ id (fun k => detCharacter d.character⁻¹ k.val * w k)
      (fun x => detCharacter d.character x * f x) g =
      detCharacter d.character g * compactCoefficient κ id w f g := by
  unfold compactCoefficient
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  simp only [id_eq, detCharacter_mul]
  calc
    _ = (detCharacter d.character⁻¹ k.val * detCharacter d.character k.val) *
          (detCharacter d.character g * (w k * f (k.val * g))) := by ring
    _ = _ := by rw [detCharacter_inv_mul, one_mul]

private theorem detCharacter_inverseTranspose (d : ComplexCharacterData) (g : G) :
    detCharacter d.character (ι g) = detCharacter d.inv.character g := by
  unfold detCharacter
  rw [Langlands.RankinSelberg.HighlyRamified.determinant_inverseTranspose,
    map_inv, Units.val_inv_eq_inv_val, ComplexCharacterData.inv_character_apply]

/-- The normalized square functional equation for the compact coefficient twisted by the
adjoining character. The positive matrix transform has epsilon parameter `a`. -/
def ComplexAdjacentTwistedZetaStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (κ : Measure K) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ) (d : ComplexCharacterData) (es : Fin (r + 1) → ComplexCharacterData)
    (Φ : 𝓢(Mat, ℂ)) (f : G → ℂ) (w : K → ℂ),
    f ∈ complexStandardModule (r + 1) (List.ofFn es) → Continuous w →
    let ds := List.ofFn fun i => (es i).mul d
    let C := compactCoefficient κ id w f
    let Z := zetaKernel Φ (fun g => detCharacter d.character g * C g)
    let Zd := zetaKernel (matrixTransform (-a) Φ)
      (fun g => detCharacter d.inv.character g * C (ι g))
    ∃ (σ : ℝ) (N Nd : ℂ → ℂ), Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
      (∀ s : ℂ, σ < s.re →
        Integrable (Z s) μ ∧ Integrable (Zd s) μ ∧
        N s = (complexLFactor ds).denominator s * ∫ g, Z s g ∂μ ∧
        Nd s = (complexLFactor (ds.map ComplexCharacterData.inv)).denominator s *
          ∫ g, Zd s g ∂μ) ∧
      ∀ s : ℂ, Nd (1 - s) =
        (complexEpsilon ds a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) * N s

theorem complexAdjacentTwistedZeta : ComplexAdjacentTwistedZetaStatement (r := r) := by
  intro μ _ κ _ _ a d es Φ f w hf hw ds C Z Zd
  let f' (g : G) := detCharacter d.character g * f g
  let w' (k : K) := detCharacter d.character⁻¹ k.val * w k
  have hf' : f' ∈ complexStandardModule (r + 1) ds := by
    change f' ∈ complexStandardModule (r + 1) (List.ofFn ((fun x : ComplexCharacterData => x.mul d) ∘ es))
    rw [← List.map_ofFn]
    exact detCharacter_mul_mem_principalSeries d.character
      (fun i z => complexPositionCharacter_map_mul d (List.ofFn es) i
        (by simpa only [List.length_ofFn] using i.isLt) z) hf
  have hw' : Continuous w' :=
    ((Units.continuous_val.comp (d.character⁻¹.continuous.comp
      determinantContinuous.continuous)).comp continuous_subtype_val).mul hw
  have hC : compactCoefficient κ id w' f' = fun g => detCharacter d.character g * C g :=
    funext (compactCoefficient_detMul κ d w f)
  obtain ⟨σ, M, Md, hM, hMd, hEq, hReflect⟩ :=
    complexSquareCoefficientFunctionalEquation μ κ (-a) (fun i => (es i).mul d) Φ f' w' hf' hw'
  refine ⟨σ, M, Md, hM, hMd, ?_, ?_⟩
  · intro s hs
    simpa only [Z, Zd, hC, detCharacter_inverseTranspose] using hEq s hs
  · simpa only [neg_neg, Units.val_neg, nnnorm_neg] using hReflect

end Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta
