import Langlands.Global.ArchimedeanConvolutionDifferentiationStatement
import Langlands.Global.ArchimedeanConvolutionRealDifferentiationProof
import Langlands.Global.ArchimedeanEnvelopingSupportProof

/-! # Smooth compact convolution and differentiation by the enveloping algebra -/

noncomputable section
universe u
open MeasureTheory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The analytic real-generator assertion suffices for all enveloping derivatives. -/
theorem compactKernelConvolutionDifferentiation_of_real
    (h : CompactKernelConvolutionRealDifferentiationStatement K n) :
    CompactKernelConvolutionDifferentiationStatement K n := by
  classical
  intro _ _ μ _ f κ
  choose S hS hD using h μ f
  have hI (a : EnvelopingAlgebra K n) (η : SmoothCompactKernel K n)
      (g : InfiniteAdelicGL K n) :
      Integrable (fun y => f y * (envelopingAction K n a η.val).val (y⁻¹ * g)) μ :=
    convolution_integrable K n μ f
      ⟨envelopingAction K n a η.val, envelopingCompactSupport K n a η.val η.property⟩ g
  have hJ (X : ComplexLieAlgebra K n) (η : SmoothCompactKernel K n)
      (g : InfiniteAdelicGL K n) :
      Integrable (fun y => f y * (complexSmoothLieAction K n X η.val).val (y⁻¹ * g)) μ := by
    simpa only [envelopingAction_generator] using hI (envelopingGenerator K n X) η g
  have hC (X : ComplexLieAlgebra K n) (η : SmoothCompactKernel K n)
      (g : InfiniteAdelicGL K n) :
      (complexSmoothLieAction K n X (S η)).val g =
        ∫ y, f y * (complexSmoothLieAction K n X η.val).val (y⁻¹ * g) ∂μ := by
    induction X using TensorProduct.inductionOn with
    | tmul z X =>
      simp only [complexSmoothLieAction_tmul, LinearMap.smul_apply, Submodule.coe_smul,
        Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_left_comm (f _) z]
      rw [integral_const_mul, hD η X g]
    | add X Y hX hY =>
      simp only [map_add, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, mul_add]
      rw [integral_add (hJ X η g) (hJ Y η g), hX, hY]
  have hA (a : EnvelopingAlgebra K n) : ∀ (η : SmoothCompactKernel K n)
      (g : InfiniteAdelicGL K n),
      (envelopingAction K n a (S η)).val g =
        ∫ y, f y * (envelopingAction K n a η.val).val (y⁻¹ * g) ∂μ := by
    obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
      (UniversalEnvelopingAlgebra.ringCon ℂ (ComplexLieAlgebra K n)) a
    change ∀ η g,
      (envelopingAction K n (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t) (S η)).val g =
        ∫ y, f y *
          (envelopingAction K n (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t) η.val).val
            (y⁻¹ * g) ∂μ
    induction t using TensorAlgebra.induction with
    | algebraMap z =>
      intro η g
      simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, LinearMap.smul_apply,
        Module.End.one_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_left_comm (f _) z]
      rw [integral_const_mul, hS η]
      rfl
    | ι X =>
      intro η g
      change (envelopingAction K n (envelopingGenerator K n X) (S η)).val g =
        ∫ y, f y * (envelopingAction K n (envelopingGenerator K n X) η.val).val (y⁻¹ * g) ∂μ
      simpa only [envelopingAction_generator] using hC X η g
    | add x y hx hy =>
      intro η g
      simp only [map_add, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, mul_add]
      rw [integral_add (hI _ η g) (hI _ η g), hx, hy]
    | mul x y hx hy =>
      intro η g
      let b := UniversalEnvelopingAlgebra.mkAlgHom ℂ (ComplexLieAlgebra K n) y
      let ηb : SmoothCompactKernel K n :=
        ⟨envelopingAction K n b η.val, envelopingCompactSupport K n b η.val η.property⟩
      have hb : envelopingAction K n b (S η) = S ηb := by
        apply Subtype.ext
        funext z
        exact (hy η z).trans (congrFun (hS ηb) z).symm
      simp only [map_mul, Module.End.mul_apply]
      change (envelopingAction K n (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ x)
        (envelopingAction K n b (S η))).val g = _
      rw [hb]
      exact hx ηb g
  exact ⟨S κ, hS κ, fun a g => hA a κ g⟩

/-- The actual raw convolution is smooth, and every enveloping derivative transfers
to its compact kernel. -/
theorem compactKernelConvolutionDifferentiation :
    CompactKernelConvolutionDifferentiationStatement K n :=
  compactKernelConvolutionDifferentiation_of_real K n
    (compactKernelConvolutionRealDifferentiation K n)

end Langlands.Global.ArchimedeanGL
