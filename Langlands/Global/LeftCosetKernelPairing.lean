import Langlands.Global.LeftCosetDiagonalSwap

/-! # Transposition of a kernel pairing on a left Haar quotient -/

noncomputable section

universe u

open MeasureTheory

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H] [LocallyCompactSpace H]
  [PolishSpace H] (Γ : Subgroup H) (hΓ : IsDiscrete (Γ : Set H))
  [(Measure.haar : Measure H).IsMulRightInvariant]

local notation "X" => LeftCosetSpace Γ
local notation "dx" => haarQuotientMeasure Γ hΓ
local notation "dh" => (Measure.haar : Measure H)

private theorem integral_integral_swap_diagonal_of_integrable_transpose (Φ : H → H → ℂ)
    (hinv : ∀ (r : Γ) (x y : H), Φ ((r : H) * x) ((r : H) * y) = Φ x y)
    (hint : Integrable (fun p : X × H =>
      Φ (Quotient.out p.1 * p.2⁻¹) (Quotient.out p.1)) (Measure.prod dx dh)) :
    ∫ ξ : X, ∫ y, Φ (Quotient.out ξ) y ∂dh ∂dx =
      ∫ η : X, ∫ x, Φ x (Quotient.out η) ∂dh ∂dx := by
  let := ConstantTermAverage.isInvInvariant_of_isMulRightInvariant dh
  let := isLocallyFiniteMeasure_haarQuotientMeasure Γ hΓ
  let := discreteQuotientBorelSpace Γ hΓ
  let G₁ (p : X × H) := Φ (Quotient.out p.1) (Quotient.out p.1 * p.2)
  let G₂ (p : X × H) := Φ (Quotient.out p.1 * p.2⁻¹) (Quotient.out p.1)
  let S (p : X × H) := (rightTranslate Γ p.2 p.1, p.2)
  have hS : MeasurePreserving S (Measure.prod dx dh) (Measure.prod dx dh) := by
    have hsk : MeasurePreserving (fun p : H × X => (p.1, rightTranslate Γ p.1 p.2))
        (Measure.prod dh dx) (Measure.prod dh dx) := by
      refine MeasurePreserving.skew_product (MeasurePreserving.id dh) ?_ ?_
      · exact (continuous_smul.comp ((MulOpposite.continuous_op.comp continuous_fst).prodMk
          continuous_snd)).measurable
      · exact Filter.Eventually.of_forall fun z =>
          (measurePreserving_rightTranslate_haarQuotientMeasure Γ hΓ z).map_eq
    exact (Measure.measurePreserving_swap (μ := dh) (ν := dx)).comp
      (hsk.comp (Measure.measurePreserving_swap (μ := dx) (ν := dh)))
  have hG : ∀ p, G₂ (S p) = G₁ p := by
    rintro ⟨ξ, z⟩
    obtain ⟨x, rfl⟩ := mk_surjective Γ ξ
    change Φ (Quotient.out (rightTranslate Γ z (mk Γ x)) * z⁻¹)
      (Quotient.out (rightTranslate Γ z (mk Γ x))) = Φ (Quotient.out (mk Γ x)) _
    rw [rightTranslate_mk]
    obtain ⟨r, hr⟩ := exists_out_eq Γ (x * z)
    obtain ⟨s, hs⟩ := exists_out_eq Γ x
    rw [hr, hs, mul_assoc, mul_inv_cancel_right, hinv, mul_assoc, hinv]
  have hint₁ : Integrable G₁ (Measure.prod dx dh) :=
    (hS.integrable_comp_of_integrable hint).congr (Filter.Eventually.of_forall hG)
  calc
    ∫ ξ, ∫ y, Φ (Quotient.out ξ) y ∂dh ∂dx =
        ∫ ξ, ∫ z, G₁ (ξ, z) ∂dh ∂dx := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      exact (integral_mul_left_eq_self (fun y => Φ (Quotient.out ξ) y) (Quotient.out ξ)).symm
    _ = ∫ p, G₁ p ∂(Measure.prod dx dh) := (integral_prod _ hint₁).symm
    _ = ∫ p, G₂ (S p) ∂(Measure.prod dx dh) :=
      integral_congr_ae (Filter.Eventually.of_forall fun p => (hG p).symm)
    _ = ∫ p, G₂ p ∂(Measure.prod dx dh) := by
      conv_rhs => rw [← hS.map_eq]
      apply (integral_map hS.measurable.aemeasurable ?_).symm
      rw [hS.map_eq]
      exact hint.aestronglyMeasurable
    _ = ∫ η, ∫ z, G₂ (η, z) ∂dh ∂dx := integral_prod _ hint
    _ = ∫ η, ∫ x, Φ x (Quotient.out η) ∂dh ∂dx := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
      have h := integral_div_left_eq_self (fun x => Φ x (Quotient.out η)) dh (Quotient.out η)
      simpa only [div_eq_mul_inv] using h

/-- An integrable kernel can be transposed in a quotient pairing between an integrable
function and a bounded measurable function. -/
theorem integral_integral_kernel_swap (K : H → ℂ) (hK : Integrable K dh)
    (v t : X → ℂ) (hv : Integrable v dx) (ht : Measurable t) (C : ℝ)
    (htC : ∀ q, ‖t q‖ ≤ C) :
    ∫ ξ : X, (∫ y, K ((Quotient.out ξ)⁻¹ * y) * v (mk Γ y) ∂dh) *
        starRingEnd ℂ (t ξ) ∂dx =
      ∫ η : X, v η * (∫ x, K (x⁻¹ * Quotient.out η) *
        starRingEnd ℂ (t (mk Γ x)) ∂dh) ∂dx := by
  let := isLocallyFiniteMeasure_haarQuotientMeasure Γ hΓ
  let := discreteQuotientBorelSpace Γ hΓ
  let Φ (x y : H) := K (x⁻¹ * y) * v (mk Γ y) * starRingEnd ℂ (t (mk Γ x))
  have hInv (r : Γ) (x y : H) : Φ ((r : H) * x) ((r : H) * y) = Φ x y := by
    simp only [Φ, mk_subgroup_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hout (q : X) : mk Γ (Quotient.out q) = q := Quotient.out_eq q
  let t₂ (p : X × H) := t (rightTranslate Γ p.2⁻¹ p.1)
  have ht₂ : Measurable t₂ := ht.comp (continuous_smul.comp
    ((MulOpposite.continuous_op.comp continuous_snd.inv).prodMk continuous_fst)).measurable
  have hG (p : X × H) :
      Φ (Quotient.out p.1 * p.2⁻¹) (Quotient.out p.1) =
        K p.2 * v p.1 * starRingEnd ℂ (t₂ p) := by
    have ht' : mk Γ ((Quotient.out p.1 : H) * p.2⁻¹) = rightTranslate Γ p.2⁻¹ p.1 := by
      rw [← rightTranslate_mk, hout]
    simp only [Φ, t₂, ht', mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one, hout]
  have hInt : Integrable (fun p : X × H => Φ (Quotient.out p.1 * p.2⁻¹) (Quotient.out p.1))
      (Measure.prod dx dh) := by
    simp only [hG]
    apply ((hv.norm.mul_prod hK.norm).mul_const C).mono'
    · apply AEStronglyMeasurable.mul _ (continuous_star.measurable.comp ht₂).aestronglyMeasurable
      exact (hK.aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_snd (μ := dx) (ν := dh))).mul
        (hv.aestronglyMeasurable.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_fst (μ := dx) (ν := dh)))
    · refine Filter.Eventually.of_forall fun p => ?_
      rw [norm_mul, norm_mul, Complex.norm_conj, mul_comm ‖K p.2‖]
      exact mul_le_mul_of_nonneg_left (htC _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hSwap := integral_integral_swap_diagonal_of_integrable_transpose Γ hΓ Φ hInv hInt
  change (∫ ξ : X, ∫ y, K ((Quotient.out ξ)⁻¹ * y) * v (mk Γ y) *
      starRingEnd ℂ (t (mk Γ (Quotient.out ξ))) ∂dh ∂dx) =
    ∫ η : X, ∫ x, K (x⁻¹ * Quotient.out η) * v (mk Γ (Quotient.out η)) *
      starRingEnd ℂ (t (mk Γ x)) ∂dh ∂dx at hSwap
  simp only [hout] at hSwap
  simp only [← integral_mul_const, ← integral_const_mul]
  exact hSwap.trans (integral_congr_ae (Filter.Eventually.of_forall fun η =>
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)))

end Langlands.Global.LeftCosetSpace
