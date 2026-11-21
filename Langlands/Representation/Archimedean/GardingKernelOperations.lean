import Langlands.Representation.Archimedean.GardingRiesz
import Langlands.Analysis.SmoothCompactKernelConvolutionProof

noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff Pointwise ComplexConjugate

namespace Langlands.Archimedean

variable {A G : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [Group G] [TopologicalSpace G] [ChartedSpace A G] [LieGroup 𝓘(ℝ, A) ∞ G]

omit [Group G] [LieGroup 𝓘(ℝ, A) ∞ G] in
/-- Pullback of a smooth compact kernel by a smooth homeomorphism. -/
def gardingKernelPullback (e : G ≃ₜ G) (he : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, A) ∞ e) :
    smoothCompactKernels A G →ₗ[ℂ] smoothCompactKernels A G where
  toFun f := ⟨f.val ∘ e, ⟨f.property.1.comp he, f.property.2.comp_homeomorph e⟩⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

omit [Group G] [LieGroup 𝓘(ℝ, A) ∞ G] in
/-- Pullback by a diffeomorphism is an equivalence of smooth compact kernels. -/
def gardingKernelPullbackEquiv (e : G ≃ₜ G)
    (he : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, A) ∞ e)
    (he' : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, A) ∞ e.symm) :
    smoothCompactKernels A G ≃ₗ[ℂ] smoothCompactKernels A G where
  __ := gardingKernelPullback e he
  invFun := gardingKernelPullback e.symm he'
  left_inv f := Subtype.ext (funext fun x => congrArg f.val (e.apply_symm_apply x))
  right_inv f := Subtype.ext (funext fun x => congrArg f.val (e.symm_apply_apply x))

section Translation

variable [IsTopologicalGroup G]

/-- The left translation `x ↦ f(a⁻¹ x)` on kernels. -/
def gardingKernelLeft (a : G) : smoothCompactKernels A G →ₗ[ℂ] smoothCompactKernels A G :=
  gardingKernelPullback (Homeomorph.mulLeft a⁻¹) contMDiff_mul_left

/-- The right translation `x ↦ f(x a)` on kernels. -/
def gardingKernelRight (a : G) : smoothCompactKernels A G →ₗ[ℂ] smoothCompactKernels A G :=
  gardingKernelPullback (Homeomorph.mulRight a) contMDiff_mul_right

@[simp] theorem gardingKernelLeft_apply (a : G) (f : smoothCompactKernels A G) (x : G) :
    (gardingKernelLeft a f).val x = f.val (a⁻¹ * x) := rfl

@[simp] theorem gardingKernelRight_apply (a : G) (f : smoothCompactKernels A G) (x : G) :
    (gardingKernelRight a f).val x = f.val (x * a) := rfl

end Translation

@[simp]
theorem adjointGardingKernel_adjoint (f : smoothCompactKernels A G) :
    adjointGardingKernel (adjointGardingKernel f) = f :=
  Subtype.ext (funext fun x => by
    change conj (conj (f.val x⁻¹⁻¹)) = _
    rw [inv_inv, starRingEnd_self_apply])

/-- Conjugate inversion as a semilinear equivalence of the test space. -/
def adjointGardingKernelEquiv : smoothCompactKernels A G ≃ₗ⋆[ℂ] smoothCompactKernels A G where
  toFun := adjointGardingKernel
  invFun := adjointGardingKernel
  left_inv := adjointGardingKernel_adjoint
  right_inv := adjointGardingKernel_adjoint
  map_add' f g := Subtype.ext (funext fun x => map_add (starRingEnd ℂ) (f.val x⁻¹) (g.val x⁻¹))
  map_smul' c f := Subtype.ext (funext fun x => map_mul (starRingEnd ℂ) c (f.val x⁻¹))

variable [IsTopologicalGroup G]

@[simp] theorem adjointGardingKernel_left (a : G) (f : smoothCompactKernels A G) :
    adjointGardingKernel (gardingKernelLeft a f) =
      gardingKernelRight a (adjointGardingKernel f) := by
  apply Subtype.ext
  funext x
  change conj (f.val (a⁻¹ * x⁻¹)) = conj (f.val (x * a)⁻¹)
  rw [mul_inv_rev]

@[simp] theorem adjointGardingKernel_right (a : G) (f : smoothCompactKernels A G) :
    adjointGardingKernel (gardingKernelRight a f) =
      gardingKernelLeft a (adjointGardingKernel f) := by
  apply Subtype.ext
  funext x
  change conj (f.val (x⁻¹ * a)) = conj (f.val (a⁻¹ * x)⁻¹)
  rw [mul_inv_rev, inv_inv]

variable [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

/-- Scalar convolution as a smooth compact kernel. -/
def gardingKernelConvolution (f g : smoothCompactKernels A G) : smoothCompactKernels A G := by
  let c (x : G) : ℂ := ∫ a, f.val a * g.val (a⁻¹ * x) ∂μ
  have hc : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ c := by
    simpa only [c, smul_eq_mul, ContinuousMap.coe_mk, mul_comm] using
      (Langlands.Analysis.smoothCompactKernelConvolution A G ℂ μ
        ⟨f.val, f.property.1.continuous⟩ g.val g.property.1 g.property.2).2
  refine ⟨c, hc, ?_⟩
  have hK : IsCompact (tsupport f.val * tsupport g.val) := f.property.2.mul g.property.2
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal (fun x hx => ?_) hK.isClosed)
  by_contra hn
  apply hx
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro a
  by_contra h
  apply hn
  exact Set.mem_mul.mpr ⟨a, subset_tsupport _ (left_ne_zero_of_mul h), a⁻¹ * x,
    subset_tsupport _ (right_ne_zero_of_mul h), by simp⟩

@[simp] theorem gardingKernelConvolution_apply (f g : smoothCompactKernels A G) (x : G) :
    (gardingKernelConvolution μ f g).val x = ∫ a, f.val a * g.val (a⁻¹ * x) ∂μ := rfl

/-- Conjugate inversion reverses the order of convolution. -/
theorem adjointGardingKernel_convolution [μ.IsMulLeftInvariant] (f g : smoothCompactKernels A G) :
    adjointGardingKernel (gardingKernelConvolution μ f g) =
      gardingKernelConvolution μ (adjointGardingKernel g) (adjointGardingKernel f) := by
  apply Subtype.ext
  funext x
  change conj (∫ a, f.val a * g.val (a⁻¹ * x⁻¹) ∂μ) =
    ∫ a, conj (g.val a⁻¹) * conj (f.val (a⁻¹ * x)⁻¹) ∂μ
  rw [← integral_conj, ← integral_mul_left_eq_self
    (fun a => conj (f.val a * g.val (a⁻¹ * x⁻¹))) x⁻¹]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro a
  simp only [mul_inv_rev, inv_inv, mul_inv_cancel_right, map_mul]
  exact mul_comm _ _

end Langlands.Archimedean
