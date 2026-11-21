import Langlands.Global.RankinSelberg.ComplexLocalCompactWeight
import Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement

/-! # Inserting the compact weight in a complex matrix integral -/

noncomputable section

open MeasureTheory

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

section Haar

variable {K G : Type*} [Group K] [MeasurableSpace K] [MeasurableInv K]
  [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

private def compactLeftShear (i : K →* G) (hi : Measurable i) : K × G ≃ᵐ K × G where
  toFun z := (z.1, i z.1 * z.2)
  invFun z := (z.1, i z.1⁻¹ * z.2)
  left_inv := by rintro ⟨k, g⟩; simp only [map_inv, inv_mul_cancel_left]
  right_inv := by rintro ⟨k, g⟩; simp only [map_inv, mul_inv_cancel_left]
  measurable_toFun := measurable_fst.prodMk ((hi.comp measurable_fst).mul measurable_snd)
  measurable_invFun := measurable_fst.prodMk ((hi.comp measurable_fst.inv).mul measurable_snd)

private theorem measurePreserving_compactLeftShear (i : K →* G) (hi : Measurable i)
    (ν : Measure K) (μ : Measure G) [SFinite ν] [SFinite μ] [μ.IsMulLeftInvariant] :
    MeasurePreserving (compactLeftShear i hi) (ν.prod μ) (ν.prod μ) :=
  (MeasurePreserving.id ν).skew_product ((hi.comp measurable_fst).mul measurable_snd)
    (Filter.Eventually.of_forall fun k => (measurePreserving_mul_left μ (i k)).map_eq)

private theorem compactLeftShear_comp (i : K →* G) (hi : Measurable i)
    (κ : K → ℂ) (A F : G → ℂ) :
    (fun p : K × G => κ p.1 * A (i p.1⁻¹ * p.2) * F p.2) ∘ compactLeftShear i hi =
      fun p => A p.2 * (κ p.1 * F (i p.1 * p.2)) := by
  funext p
  rcases p with ⟨k, g⟩
  change κ k * A (i k⁻¹ * (i k * g)) * F (i k * g) = _
  rw [map_inv, inv_mul_cancel_left]
  ac_rfl

/-- The compact shear transfers absolute integrability to the kernel with unshifted test. -/
theorem integrable_compact_average_iff (i : K →* G) (hi : Measurable i)
    (ν : Measure K) (μ : Measure G) [SFinite ν] [SFinite μ] [μ.IsMulLeftInvariant]
    (κ : K → ℂ) (A F : G → ℂ) :
    Integrable (fun p : K × G => κ p.1 * A (i p.1⁻¹ * p.2) * F p.2) (ν.prod μ) ↔
      Integrable (fun p : K × G => A p.2 * (κ p.1 * F (i p.1 * p.2))) (ν.prod μ) := by
  rw [← compactLeftShear_comp i hi κ A F]
  exact ((measurePreserving_compactLeftShear i hi ν μ).integrable_comp_emb
    (compactLeftShear i hi).measurableEmbedding).symm

/-- A reproducing weighted test permits insertion of the same compact weight
on the coefficient, by Haar left translation and Fubini. -/
theorem integral_of_compact_average (i : K →* G) (hi : Measurable i)
    (ν : Measure K) (μ : Measure G) [SFinite ν] [SFinite μ] [μ.IsMulLeftInvariant]
    (κ : K → ℂ) (A F : G → ℂ)
    (hA : ∀ g, A g = ∫ k, κ k * A (i k⁻¹ * g) ∂ν)
    (hInt : Integrable (fun p : K × G => κ p.1 * A (i p.1⁻¹ * p.2) * F p.2) (ν.prod μ)) :
    (∫ g, A g * F g ∂μ) = ∫ g, A g * (∫ k, κ k * F (i k * g) ∂ν) ∂μ := by
  let e := compactLeftShear i hi
  have he := measurePreserving_compactLeftShear i hi ν μ
  let H (p : K × G) := κ p.1 * A (i p.1⁻¹ * p.2) * F p.2
  let B (p : K × G) := A p.2 * (κ p.1 * F (i p.1 * p.2))
  have hB : H ∘ e = B := compactLeftShear_comp i hi κ A F
  have hBInt : Integrable B (ν.prod μ) :=
    (integrable_compact_average_iff i hi ν μ κ A F).mp hInt
  calc
    _ = ∫ p, H p ∂ν.prod μ := by
      rw [integral_prod_symm H hInt]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun g => ?_
      change A g * F g = ∫ k, κ k * A (i k⁻¹ * g) * F g ∂ν
      rw [hA, integral_mul_const]
    _ = ∫ p, H (e p) ∂ν.prod μ := (he.integral_comp e.measurableEmbedding H).symm
    _ = ∫ p, B p ∂ν.prod μ := by rw [← hB]; rfl
    _ = _ := by
      rw [integral_prod_symm B hBInt]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun g => ?_
      change (∫ k, A g * (κ k * F (i k * g)) ∂ν) = _
      exact integral_const_mul _ _

/-- Insert the reproducing weight, expand its compact average, and separate
the quotient and group factors. -/
theorem integral_prod_eq_sum_mul_of_compact_average {Q : Type*} [MeasurableSpace Q]
    (i : K →* G) (hi : Measurable i)
    (ν : Measure K) (μ : Measure G) (ρ : Measure Q)
    [SFinite ν] [SFinite μ] [SFinite ρ] [μ.IsMulLeftInvariant]
    (κ : K → ℂ) (A : G → ℂ) (F : Q → G → ℂ)
    (hA : ∀ g, A g = ∫ k, κ k * A (i k⁻¹ * g) ∂ν)
    (hProd : Integrable (fun p : Q × G => A p.2 * F p.1 p.2) (ρ.prod μ))
    (hInt : ∀ᵐ q ∂ρ, Integrable
      (fun p : K × G => κ p.1 * A (i p.1⁻¹ * p.2) * F q p.2) (ν.prod μ))
    {d : ℕ} (a : Fin d → Q → ℂ) (b : Fin d → G → ℂ)
    (hExp : ∀ q g, (∫ k, κ k * F q (i k * g) ∂ν) = ∑ j, a j q * b j g)
    (ha : ∀ j, Integrable (a j) ρ)
    (hb : ∀ j, Integrable (fun g => A g * b j g) μ) :
    (∫ g, A g * (∫ q, F q g ∂ρ) ∂μ) =
      ∑ j, (∫ q, a j q ∂ρ) * (∫ g, A g * b j g ∂μ) := by
  let S (j : Fin d) := ∫ g, A g * b j g ∂μ
  calc
    _ = ∫ p : Q × G, A p.2 * F p.1 p.2 ∂ρ.prod μ := by
      rw [integral_prod_symm _ hProd]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g => (integral_const_mul (A g) _).symm
    _ = ∫ q, ∫ g, A g * F q g ∂μ ∂ρ := integral_prod _ hProd
    _ = ∫ q, ∑ j, a j q * S j ∂ρ := by
      apply integral_congr_ae
      filter_upwards [hInt] with q hq
      rw [integral_of_compact_average i hi ν μ κ A (F q) hA hq]
      simp_rw [hExp, Finset.mul_sum]
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [show (fun g => A g * (a j q * b j g)) = fun g => a j q * (A g * b j g) by
          funext g
          rw [mul_left_comm]]
        exact integral_const_mul _ _
      · intro j _
        exact (hb j).const_mul (a j q) |>.congr
          (Filter.Eventually.of_forall fun g => mul_left_comm _ _ _)
    _ = _ := by
      rw [integral_finsetSum]
      · simp only [integral_mul_const, S]
      · exact fun j _ => (ha j).mul_const (S j)

end Haar

section MatrixIntegral

open Langlands.Archimedean ArchimedeanLocal
open scoped Langlands.Archimedean.ComplexDuality

variable {r : ℕ}

local notation "n" => r + 1
local notation "Kc" => unitaryCompact ℂ n
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel

local instance averagingMatrixSecondCountable : SecondCountableTopology Mat :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
local instance averagingOppositeSecondCountable : SecondCountableTopology Matᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology
local instance averagingGroupSecondCountable : SecondCountableTopology G :=
  Units.isInducing_embedProduct.secondCountableTopology

private theorem determinant_norm_unitary (k : Kc) : ‖k.val.val.det‖ = 1 := by
  let z := k.val.val.det
  have hz : z * star z = 1 := (Matrix.det_of_mem_unitary k.2).2
  have hsq : (‖z‖ ^ 2 : ℝ) = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_one, Complex.ofReal_pow, ← Complex.mul_conj', starRingEnd_apply, hz]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (hsq.trans (one_pow 2).symm)

/-- The square test together with its determinant character and norm power. -/
def complexWeightedMatrixTest (η : ℂˣ →* ℂˣ) (Φ : Mat → ℂ) (s : ℂ) (g : G) : ℂ :=
  Φ g.val * (η (GeneralLinear.determinant g) : ℂ) * ArchimedeanLocal.detPower complexNormalizedAbs g s

theorem complexWeightedMatrixTest_reproduce
    (i : Kc → Kc) (ν : Measure Kc) (η : ℂˣ →* ℂˣ) (Φ : Mat → ℂ) (κ : Kc → ℂ)
    (hΦ : ∀ X, ∫ k, κ k * complexCompactMatrixTranslate (η.comp invMonoidHom) Φ (i k) X ∂ν = Φ X)
    (s : ℂ) (g : G) :
    complexWeightedMatrixTest η Φ s g =
      ∫ k, κ k * complexWeightedMatrixTest η Φ s ((i k).val⁻¹ * g) ∂ν := by
  let χ : ℂ := η (GeneralLinear.determinant g)
  let P : G → ℂ → ℂ := ArchimedeanLocal.detPower complexNormalizedAbs
  change Φ g.val * χ * P g s = _
  rw [← hΦ g.val, ← integral_mul_const, ← integral_mul_const]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun k => ?_
  let u := i k
  have hd : ‖(u.val⁻¹ : G).val.det‖ = 1 := by
    change ‖(GeneralLinear.determinant u.val⁻¹ : ℂ)‖ = 1
    rw [map_inv, Units.val_inv_eq_inv_val, norm_inv]
    exact inv_eq_one.mpr (determinant_norm_unitary u)
  have hp : P (u.val⁻¹ * g) s = P g s := by
    simp only [P, ArchimedeanLocal.detPower, Units.val_mul, Matrix.det_mul,
      complexNormalizedAbs, norm_mul, hd, one_mul]
  change κ k * complexCompactMatrixTranslate (η.comp invMonoidHom) Φ u g.val * χ * P g s =
    κ k * (Φ (u.val⁻¹ * g).val * (η (GeneralLinear.determinant (u.val⁻¹ * g)) : ℂ) *
      P (u.val⁻¹ * g) s)
  simp only [hp, complexCompactMatrixTranslate, χ, map_mul, Units.val_mul,
    MonoidHom.comp_apply, invMonoidHom_apply, map_inv]
  ring

variable (r) in
/-- An unfolded integral separates as a finite sum of quotient integrals
times weighted square-matrix integrals under the indicated compact expansion. -/
def ComplexLocalCompactIntegralExpansionStatement : Prop :=
  ∀ (Q : Type) [MeasurableSpace Q] (ρ : Measure Q) [SFinite ρ],
  ∀ (ν : Measure Kc) [SFinite ν] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant],
  ∀ (i : Kc →* Kc), Measurable i →
  ∀ (η : ℂˣ →* ℂˣ) (Φ : Mat → ℂ) (κ : Kc → ℂ) (s : ℂ) (F : Q → G → ℂ),
    (∀ X, ∫ k, κ k * complexCompactMatrixTranslate (η.comp invMonoidHom) Φ (i k) X ∂ν = Φ X) →
    let A := complexWeightedMatrixTest η Φ s
    Integrable (fun p : Q × G => A p.2 * F p.1 p.2) (ρ.prod μ) →
    (∀ᵐ q ∂ρ, Integrable (fun p : Kc × G =>
      κ p.1 * A ((i p.1).val⁻¹ * p.2) * F q p.2) (ν.prod μ)) →
  ∀ (d : ℕ) (a : Fin d → Q → ℂ) (b : Fin d → G → ℂ),
    (∀ q g, (∫ k, κ k * F q ((i k).val * g) ∂ν) = ∑ j, a j q * b j g) →
    (∀ j, Integrable (a j) ρ) →
    (∀ j, Integrable (fun g => A g * b j g) μ) →
    (∫ g, A g * (∫ q, F q g ∂ρ) ∂μ) =
      ∑ j, (∫ q, a j q ∂ρ) * (∫ g, A g * b j g ∂μ)

theorem complexLocalCompactIntegralExpansion : ComplexLocalCompactIntegralExpansionStatement r := by
  intro Q _ ρ _ ν _ μ _ _ i hi η Φ κ s F hΦ A hProd hInt d a b hExp ha hb
  refine integral_prod_eq_sum_mul_of_compact_average ((unitaryCompact ℂ n).subtype.comp i)
    (continuous_subtype_val.measurable.comp hi) ν μ ρ κ A F ?_ hProd ?_ a b hExp ha hb
  · simp only [map_inv]
    exact complexWeightedMatrixTest_reproduce i ν η Φ κ hΦ s
  · simp only [map_inv]
    exact hInt

end MatrixIntegral

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
