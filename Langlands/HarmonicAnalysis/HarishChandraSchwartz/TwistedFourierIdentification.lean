import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TwistedFourierFamily

/-! # The Fourier transform at a twist `ω ⊗ χ`

Draft.
-/

noncomputable section

open MeasureTheory Filter Langlands.Plancherel
open Langlands.HarmonicAnalysis.TorusFourier
open scoped ComplexConjugate NNReal ENNReal TensorProduct

namespace Langlands.HarishChandraSchwartz

universe u v

section Identification

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [Nonempty (CompactOpenSubgroup G)]
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (A : SmoothRep.{0, u, v} ℂ G) (hw : L2Weights μ Ξ σ) (hA : IsAdmissible A.representation)
  (hT : HasTemperedCoefficients Ξ σ A.representation)
  (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
  (hA' : IsAdmissible (A.twist χ hχ).representation)
  (hT' : HasTemperedCoefficients Ξ σ (A.twist χ hχ).representation)

/-- Remove the twist from the dual factor of a coefficient tensor of `A ⊗ χ`: the identity on
`A` tensored with the identification of the smooth duals of `A ⊗ χ` and `A`, which keeps the
underlying linear functional. -/
def twistTensorEquiv : CoefficientTensor (A.twist χ hχ) ≃ₗ[ℂ] CoefficientTensor A :=
  TensorProduct.congr (LinearEquiv.refl ℂ A)
    (smoothContragredientTwistEquiv χ A.representation hχ).toLinearEquiv

omit [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [Nonempty (CompactOpenSubgroup G)] in
/-- The endomorphism of a tensor does not change when the twist is removed. -/
theorem coefficientTensorToEnd_twistTensorEquiv (t : CoefficientTensor (A.twist χ hχ)) :
    coefficientTensorToEnd A (twistTensorEquiv A χ hχ t) =
      coefficientTensorToEnd (A.twist χ hχ) t := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- **`(ω ⊗ χ)(f) = ω(f χ)`** as tensors: for `χ(g) = ∏ⱼ zⱼ^{n(g)ⱼ}`, removing the twist from
the tensor of `(A ⊗ χ)(φ)` gives the tensor of `A(φ χ)`. -/
theorem twistTensorEquiv_schwartzActionTensor {J : Type*} [Fintype J] {n : G → J → ℤ}
    (hn : ∀ g h, n (g * h) = n g + n h) {K₀ : CompactOpenSubgroup G}
    (hK₀ : ∀ k ∈ K₀.toSubgroup, n k = 0) (z : J → Circle)
    (hχn : ∀ g, ((χ g : ℂˣ) : ℂ) = torusCharacter (n g) z) (φ : Space Ξ σ) :
    twistTensorEquiv A χ hχ (schwartzActionTensor (A.twist χ hχ) hw hA' hT' φ) =
      schwartzActionTensor A hw hA hT (Space.twist hn hK₀ z φ) := by
  symm
  refine schwartzActionTensor_eq_of_coefficientTensorToEnd_eq A hw hA hT ?_
  rw [coefficientTensorToEnd_twistTensorEquiv, coefficientTensorToEnd_schwartzActionTensor]
  refine LinearMap.ext fun w => ext_smoothDual hA.1 fun ℓ => ?_
  let ℓ' : SmoothDual (A.twist χ hχ).representation :=
    (smoothContragredientTwistEquiv χ A.representation hχ).symm ℓ
  change ℓ'.val (schwartzAction hw hA' hT' φ w) = ℓ.val (schwartzAction hw hA hT _ w)
  rw [schwartzAction_eval, schwartzAction_eval]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  change φ g * ℓ.val (((χ g : ℂˣ) : ℂ) • A.representation g w) =
    φ g * torusCharacter (n g) z * ℓ.val (A.representation g w)
  rw [map_smul, smul_eq_mul, hχn]
  ring

end Identification

section Family

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [Nonempty (CompactOpenSubgroup G)]
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (A : SmoothRep.{0, u, v} ℂ G) (hw : L2Weights μ Ξ σ) (hA : IsAdmissible A.representation)
  (hT : HasTemperedCoefficients Ξ σ A.representation)
  {J : Type*} [Fintype J] {n : G → J → ℤ} (hn : ∀ g h, n (g * h) = n g + n h)
  {K₀ : CompactOpenSubgroup G} (hK₀ : ∀ k ∈ K₀.toSubgroup, n k = 0) (hnm : Measurable n)
  {C : ℝ} (hnσ : ∀ g, ‖n g‖ ≤ C * (1 + σ g))
  (χ : (J → Circle) → G →* ℂˣ) (hχ : ∀ z, IsOpen ((χ z).ker : Set G))
  (hχn : ∀ z g, ((χ z g : ℂˣ) : ℂ) = torusCharacter (n g) z)
  (hA' : ∀ z, IsAdmissible (A.twist (χ z) (hχ z)).representation)
  (hT' : ∀ z, HasTemperedCoefficients Ξ σ (A.twist (χ z) (hχ z)).representation)
  (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)

include hA hT hn hK₀ hnm hnσ hχn in
/-- **The Fourier transform along the twists `A ⊗ χ_z` is smooth in `z`** (Waldspurger,
Proposition VII.1.3 for `M = G`, in torus coordinates): with the twist removed from the dual
factor, `z ↦ (A ⊗ χ_z)^(d)(f) = d · (A ⊗ χ_z)(f̌)` is a finite smooth family in `A ⊗ Ã`. -/
theorem twistTensorEquiv_coefficientFourierTransform_mem_finiteSmoothFamilies (d : ℝ)
    (f : Space Ξ σ) :
    (fun z => twistTensorEquiv A (χ z) (hχ z)
      (coefficientFourierTransform (A.twist (χ z) (hχ z)) hw (hA' z) (hT' z) hΞ hσ d f)) ∈
      finiteSmoothFamilies J (CoefficientTensor A) := by
  have heq : (fun z => twistTensorEquiv A (χ z) (hχ z)
      (coefficientFourierTransform (A.twist (χ z) (hχ z)) hw (hA' z) (hT' z) hΞ hσ d f)) =
      (d : ℂ) • fun z => schwartzActionTensor A hw hA hT
        (Space.twist hn hK₀ z (Space.check hΞ hσ f)) := by
    funext z
    rw [coefficientFourierTransform_apply, map_smul,
      twistTensorEquiv_schwartzActionTensor A hw hA hT (χ z) (hχ z) (hA' z) (hT' z) hn hK₀ z
        (hχn z)]
    rfl
  rw [heq]
  exact (finiteSmoothFamilies J (CoefficientTensor A)).smul_mem _
    (schwartzActionTensor_twist_mem_finiteSmoothFamilies A hw hA hT hn hK₀ hnm hnσ _)

end Family

end Langlands.HarishChandraSchwartz
