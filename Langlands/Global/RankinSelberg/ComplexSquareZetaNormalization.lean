import Langlands.Global.RankinSelberg.ComplexSquareZetaProductTate
import Langlands.Global.RankinSelberg.ComplexTateProductContinuation

/-! # Entire normalization of the complex square zeta integral -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator NNReal SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

open Langlands.Archimedean Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open ComplexSquareFourier (upperMarginal)
open ComplexTateProduct (IsEntireNormalization affineParameter normalizedZeta gammaNormalizer)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance squareNormalizationGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance squareNormalizationGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "Z" => Fin n → ℂ
local notation "W" => Fin n → ℤ

/-- The diagonal Schwartz test obtained by compact averaging and strictly upper integration. -/
def diagonalTest (κ : Measure K) [IsFiniteMeasure κ] (a : ℂˣ) (Φ : 𝓢(Mat, ℂ))
    (f : G → ℂ) (hf : Continuous f) : 𝓢(Z, ℂ) :=
  upperMarginal a (rightAverage κ (fun k => f k.val) (hf.comp continuous_subtype_val) Φ)

theorem denominator_complexLFactor_ofFn (ds : Fin n → ComplexCharacterData) (s : ℂ) :
    (complexLFactor (List.ofFn ds)).denominator s =
      ∏ j, gammaNormalizer (ds j).weight (s + (ds j).exponent) := by
  rw [denominator_complexLFactor, List.map_ofFn, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro j _
  simp only [ComplexCharacterData.lFactor, complexTateL, ReciprocalEntire.shift, gammaComplex,
    gammaNormalizer, Function.comp_apply, add_assoc]

theorem denominator_complexLFactor_reverse_inv (ds : Fin n → ComplexCharacterData) (s : ℂ) :
    (complexLFactor (List.ofFn fun j => (ds j.rev).inv)).denominator s =
      (complexLFactor ((List.ofFn ds).map ComplexCharacterData.inv)).denominator s := by
  rw [List.map_ofFn, denominator_complexLFactor_ofFn, denominator_complexLFactor_ofFn]
  exact Fintype.prod_equiv Fin.revPerm _ _ fun _ => rfl

/-- The angular character at the shifted Tate parameter has the original block's epsilon. -/
theorem epsilon_ofFn_shift (ds : Fin n → ComplexCharacterData) (a : ℂˣ) (s : ℂ) :
    (∏ j, ((characterOfParams (ds j).weight 0).epsilon (-a) ‖(a : ℂ)‖₊
      (nnnorm_pos.mpr a.ne_zero) (s + (ds j).exponent) : ℂ)) =
      (complexEpsilon (List.ofFn ds) (-a) ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) := by
  rw [complexEpsilon, List.map_ofFn, List.prod_ofFn]
  change _ = Units.coeHom ℂ (∏ j, (ds j).epsilon (-a) ‖(a : ℂ)‖₊ _ s)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  let d := ds j
  change ((characterOfParams d.weight 0).epsilon (-a) ‖(a : ℂ)‖₊ _ (s + d.exponent) : ℂ) =
    (d.epsilon (-a) ‖(a : ℂ)‖₊ _ s : ℂ)
  simp only [ComplexCharacterData.coe_epsilon, ComplexCharacterData.character_eq,
    characterOfParams_weight, characterOfParams_exponent, mul_zero, Complex.cpow_zero, mul_one]
  have hne : (‖((-a : ℂˣ) : ℂ)‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (-a).ne_zero)
  rw [show 2 * (s + d.exponent - 1) = 2 * d.exponent + 2 * (s - 1) by ring,
    Complex.cpow_add _ _ hne]
  ring

/-- A fixed entire product Tate normalization yields an entire function of the single
square zeta parameter. The same positive constant applies to all inducing data at that rank. -/
def ComplexSquareZetaNormalizationStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (κ : Measure K) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ) (H : 𝓢(Z, ℂ) → W → Z → ℂ), IsEntireNormalization H →
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (ds : Fin n → ComplexCharacterData) (Φ : 𝓢(Mat, ℂ)) (f : G → ℂ)
      (hf : f ∈ complexStandardModule n (List.ofFn ds)),
      let N (s : ℂ) := (c : ℂ) * H (diagonalTest κ a Φ f hf.1.continuous)
        (fun j => (ds j).weight) (fun j => s + (ds j).exponent)
      Differentiable ℂ N ∧ ∀ s,
        Integrable (zetaKernel Φ f s) μ → (∀ j, 0 < (s + (ds j).exponent).re) →
        N s = (complexLFactor (List.ofFn ds)).denominator s * ∫ g, zetaKernel Φ f s g ∂μ

theorem complexSquareZetaNormalization : ComplexSquareZetaNormalizationStatement (n := n) := by
  intro μ hμ κ _ hκ a H hH
  obtain ⟨c, hc, hT⟩ := complexSquareZetaProductTate μ κ a hμ hκ
  refine ⟨c, hc, fun ds Φ f hf => ?_⟩
  let Ψ := diagonalTest κ a Φ f hf.1.continuous
  let m (j : Fin n) := (ds j).weight
  let u (s : ℂ) (j : Fin n) := s + (ds j).exponent
  refine ⟨?_, ?_⟩
  · have hu (s : ℂ) : affineParameter (fun j => (ds j).exponent) 1 s = u s := by
      funext j
      simp [affineParameter, u, add_comm]
    simpa only [hu] using (hH.1 Ψ m (fun j => (ds j).exponent) 1).const_mul (c : ℂ)
  · intro s hi hp
    have h := hT ds Φ f hf s hi
    change (∫ g, zetaKernel Φ f s g ∂μ) = (c : ℂ) * ComplexTateProduct.zeta Ψ m (u s) at h
    change (c : ℂ) * H Ψ m (u s) =
      (complexLFactor (List.ofFn ds)).denominator s * ∫ g, zetaKernel Φ f s g ∂μ
    rw [h, denominator_complexLFactor_ofFn, hH.2 Ψ m (u s) hp, normalizedZeta]
    change (c : ℂ) * ((∏ j, gammaNormalizer (m j) (u s j)) * ComplexTateProduct.zeta Ψ m (u s))
      = (∏ j, gammaNormalizer (m j) (u s j)) * ((c : ℂ) * ComplexTateProduct.zeta Ψ m (u s))
    ring

end Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta
