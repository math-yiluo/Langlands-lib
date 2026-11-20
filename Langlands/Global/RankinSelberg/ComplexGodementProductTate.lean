import Langlands.Global.RankinSelberg.ComplexGodementSchwartzDiagonal
import Langlands.Global.RankinSelberg.ComplexTateProductHolomorphy
import Langlands.Representation.Archimedean.ComplexJacquetBorel

/-! # Identification of the complex Godement section with a product Tate integral -/

noncomputable section

open MeasureTheory Matrix
open scoped SchwartzMap Matrix.Norms.Operator NNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC normSqC_det_unitary)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance productTateGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "H" => Langlands.GeneralLinear (n + 1) ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Z" => (Fin n → ℂ)
local notation "X" => (UpperEntryPair n → ℂ)
local notation "Rect" => Matrix (Fin n) (Fin (n + 1)) ℂ

private theorem diagonalTestKernel_at_exponent (d : ComplexCharacterData) (s : ℂ)
    (Φ : Rect → ℂ) (f : G → ℂ) (g : H) (a : Z) (k : K) (z : X) :
    diagonalTestKernel (characterOfParams d.weight (d.exponent + s)) Φ f g a k z =
      diagonalTestKernel d Φ f g a k z := by
  have hk : ‖(determinant k.val : ℂ)‖ = 1 := by
    have hs := normSqC_det_unitary k
    change ((‖(determinant k.val : ℂ)‖ ^ 2 : ℝ) : ℂ) = 1 at hs
    have hsq : ‖(determinant k.val : ℂ)‖ ^ 2 = (1 : ℝ) := by exact_mod_cast hs
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa only [one_pow] using hsq)
  unfold diagonalTestKernel
  rw [(characterOfParams d.weight (d.exponent + s)).character_eq, d.character_eq, hk]
  simp

private theorem integral_additiveDiagonalKernel_eq_zeta
    {κ : Measure K} [SigmaFinite κ] (d : ComplexCharacterData) (es : Fin n → ComplexCharacterData)
    (Φ : Rect → ℂ) (f : G → ℂ) (g : H) (Ψ : Z → ℂ) (s : ℂ)
    (hΨ : ∀ a : Z, Ψ a = ∫ z : X, ∫ k, diagonalTestKernel d Φ f g a k z ∂κ)
    (hint : Integrable (fun p : Z × (K × X) =>
      additiveDiagonalKernel (characterOfParams d.weight (d.exponent + s)) es Φ f g p.1 p.2.1 p.2.2)
      ((volume : Measure Z).prod (κ.prod (volume : Measure X)))) :
    (∫ p : Z × (K × X),
      additiveDiagonalKernel (characterOfParams d.weight (d.exponent + s)) es Φ f g p.1 p.2.1 p.2.2
      ∂((volume : Measure Z).prod (κ.prod (volume : Measure X)))) =
      ComplexTateProduct.zeta Ψ (fun j => d.weight - (es j).weight)
        (ComplexTateProduct.affineParameter (fun j => d.exponent - (es j).exponent + 1) 1 s) := by
  rw [integral_prod _ hint, ComplexTateProduct.zeta]
  apply integral_congr_ae
  filter_upwards [hint.prod_right_ae] with a ha
  let dₛ := characterOfParams d.weight (d.exponent + s)
  have hw (j : Fin n) : scalarAdditiveTateWeight dₛ (es j) (a j) =
      ComplexTateProduct.additiveWeight (d.weight - (es j).weight)
        (ComplexTateProduct.affineParameter (fun i => d.exponent - (es i).exponent + 1) 1 s j) (a j) := by
    unfold scalarAdditiveTateWeight ComplexTateProduct.additiveWeight
    by_cases hj : a j = 0
    · simp [hj]
    simp only [ite_eq_right hj, dₛ, characterOfParams_weight, characterOfParams_exponent,
      ComplexTateProduct.affineParameter, Pi.one_apply, Complex.ofReal_one, one_mul]
    congr 2
    ring
  rw [integral_prod_symm _ ha, ComplexTateProduct.integrand, hΨ]
  simp_rw [← hw, additiveDiagonalKernel, diagonalTestKernel_at_exponent, integral_mul_const, dₛ]

/-- One Schwartz test realizes the inner Godement integral as a product Tate integral for all
absolutely convergent spectral parameters, with a positive scalar depending only on the measures. -/
def ComplexGodementProductTateStatement : Prop :=
  ∀ (μ : Measure G) (κ : Measure K), μ.IsHaarMeasure → μ.IsMulRightInvariant → κ.IsHaarMeasure →
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (d : ComplexCharacterData) (es : Fin n → ComplexCharacterData)
      (Φ : 𝓢(Rect, ℂ)) (f : G → ℂ), f ∈ complexStandardModule n (List.ofFn es) → ∀ g : H,
      ∃ Ψ : 𝓢(Z, ℂ), ∀ s : ℂ,
        let dₛ := characterOfParams d.weight (d.exponent + s)
        Integrable (godementSectionIntegrand dₛ Φ f g) μ →
          (∫ h, godementSectionIntegrand dₛ Φ f g h ∂μ) =
            (c : ℂ) * ComplexTateProduct.zeta Ψ (fun j => d.weight - (es j).weight)
              (ComplexTateProduct.affineParameter (fun j => d.exponent - (es j).exponent + 1) 1 s)

theorem complexGodementProductTate : ComplexGodementProductTateStatement (n := n) := by
  intro μ κ hμ hright hκ
  let : κ.IsHaarMeasure := hκ
  let : IsFiniteMeasure κ := IsFiniteMeasure.mk (isCompact_univ.measure_lt_top (μ := κ))
  obtain ⟨c, hc, hgroup⟩ := complexGodementAdditiveDiagonal μ κ hμ hright hκ
  refine ⟨c, hc, ?_⟩
  intro d es Φ f hf g
  obtain ⟨Ψ, hΨ⟩ := complexGodementSchwartzDiagonal κ d Φ f hf.1.continuous g
  refine ⟨Ψ, fun s => ?_⟩
  dsimp only
  intro hint
  obtain ⟨hI, hE⟩ := hgroup (characterOfParams d.weight (d.exponent + s)) es Φ f Φ.continuous hf g
  exact (hE hint).trans (congrArg ((c : ℂ) * ·)
    (integral_additiveDiagonalKernel_eq_zeta d es Φ f g Ψ s hΨ (hI.mp hint)))

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
