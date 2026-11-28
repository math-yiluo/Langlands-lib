import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Data.Finsupp.SMul

/-! # The Hilbert space of a positive semidefinite kernel

For a Hermitian positive semidefinite kernel `K : ι → ι → ℂ`, the finitely supported families
`ι →₀ ℂ` carry the semi-inner product `⟨f, g⟩ = ∑ᵢ ∑ⱼ conj (f i) * g j * K i j`. Its separated
completion `K.Space` is a complex Hilbert space with vectors `K.vec i` satisfying
`⟪K.vec i, K.vec j⟫ = K i j`, whose span is dense (the Kolmogorov decomposition, or the
Moore–Aronszajn construction).

Index maps preserving the kernel induce linear isometries, and index maps satisfying a kernel
inequality induce bounded operators.
-/

noncomputable section

open scoped ComplexConjugate InnerProductSpace
open UniformSpace

namespace Langlands.Analysis

/-- The sesquilinear form `∑ᵢ ∑ⱼ conj (f i) * g j * K i j` of a kernel on finitely supported
families. -/
def kernelForm {ι : Type*} (K : ι → ι → ℂ) (f g : ι →₀ ℂ) : ℂ :=
  f.sum fun i a => g.sum fun j b => conj a * b * K i j

theorem kernelForm_add_kernel {ι : Type*} (K₁ K₂ : ι → ι → ℂ) (f g : ι →₀ ℂ) :
    kernelForm (K₁ + K₂) f g = kernelForm K₁ f g + kernelForm K₂ f g := by
  unfold kernelForm
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun j _ => ?_
  simp only [Pi.add_apply]
  ring

theorem kernelForm_smul_kernel {ι : Type*} (t : ℂ) (K : ι → ι → ℂ) (f g : ι →₀ ℂ) :
    kernelForm (t • K) f g = t * kernelForm K f g := by
  unfold kernelForm
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The form of the Gram kernel `⟪A (v i), v j⟫` is `⟪A (∑ f i • v i), ∑ g j • v j⟫`. -/
theorem kernelForm_inner {ι E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : ι → E) (A : E →L[ℂ] E) (f g : ι →₀ ℂ) :
    kernelForm (fun i j => ⟪A (v i), v j⟫_ℂ) f g =
      ⟪A (f.sum fun i a => a • v i), g.sum fun j b => b • v j⟫_ℂ := by
  unfold kernelForm
  rw [map_finsuppSum, Finsupp.sum_inner]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [Finsupp.inner_sum]
  refine Finsupp.sum_congr fun j _ => ?_
  rw [map_smul, inner_smul_left, inner_smul_right]
  ring

theorem kernelForm_mapDomain {ι ι' : Type*} (K : ι' → ι' → ℂ) (m : ι → ι') (f g : ι →₀ ℂ) :
    kernelForm K (Finsupp.mapDomain m f) (Finsupp.mapDomain m g) =
      kernelForm (fun i j => K (m i) (m j)) f g := by
  unfold kernelForm
  rw [Finsupp.sum_mapDomain_index (fun i => by simp) (fun i a₁ a₂ => ?_)]
  · refine Finsupp.sum_congr (fun i _ => ?_)
    rw [Finsupp.sum_mapDomain_index (fun j => by simp) (fun j b₁ b₂ => by ring)]
  · rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr (fun j _ => ?_)
    simp only [map_add]
    ring

/-- A Hermitian positive semidefinite kernel on `ι`. -/
structure PositiveKernel (ι : Type*) where
  /-- The values of the kernel. -/
  toFun : ι → ι → ℂ
  conj_symm' : ∀ i j, conj (toFun j i) = toFun i j
  re_nonneg' : ∀ f : ι →₀ ℂ, 0 ≤ (kernelForm toFun f f).re

namespace PositiveKernel

variable {ι : Type*} (K : PositiveKernel ι)

instance : CoeFun (PositiveKernel ι) (fun _ => ι → ι → ℂ) := ⟨PositiveKernel.toFun⟩

theorem conj_symm (i j : ι) : conj (K j i) = K i j := K.conj_symm' i j

/-- The sesquilinear form of `K` on finitely supported families. -/
def form (f g : ι →₀ ℂ) : ℂ := kernelForm K f g

theorem re_form_self_nonneg (f : ι →₀ ℂ) : 0 ≤ (K.form f f).re := K.re_nonneg' f

theorem form_add_left (f₁ f₂ g : ι →₀ ℂ) : K.form (f₁ + f₂) g = K.form f₁ g + K.form f₂ g := by
  unfold form kernelForm
  refine Finsupp.sum_add_index' (fun i => by simp) (fun i a₁ a₂ => ?_)
  rw [← Finsupp.sum_add]
  simp only [map_add, add_mul]

theorem form_add_right (f g₁ g₂ : ι →₀ ℂ) : K.form f (g₁ + g₂) = K.form f g₁ + K.form f g₂ := by
  unfold form kernelForm
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr (fun i _ => ?_)
  refine Finsupp.sum_add_index' (fun j => by simp) (fun j b₁ b₂ => ?_)
  simp only [mul_add, add_mul]

theorem form_smul_left (r : ℂ) (f g : ι →₀ ℂ) : K.form (r • f) g = conj r * K.form f g := by
  unfold form kernelForm
  rw [Finsupp.sum_smul_index' (fun i => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr (fun i _ => ?_)
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr (fun j _ => ?_)
  simp only [smul_eq_mul, map_mul]
  ring

theorem form_smul_right (r : ℂ) (f g : ι →₀ ℂ) : K.form f (r • g) = r * K.form f g := by
  unfold form kernelForm
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr (fun i _ => ?_)
  rw [Finsupp.sum_smul_index' (fun j => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr (fun j _ => ?_)
  simp only [smul_eq_mul]
  ring

theorem conj_form (f g : ι →₀ ℂ) : conj (K.form g f) = K.form f g := by
  unfold form kernelForm
  rw [map_finsuppSum, Finsupp.sum_comm]
  refine Finsupp.sum_congr (fun i _ => ?_)
  rw [map_finsuppSum]
  refine Finsupp.sum_congr (fun j _ => ?_)
  simp only [map_mul, starRingEnd_self_apply]
  rw [← K.conj_symm i j]
  simp only [starRingEnd_self_apply]
  ring

theorem form_single_single (i j : ι) (a b : ℂ) :
    K.form (Finsupp.single i a) (Finsupp.single j b) = conj a * b * K i j := by
  unfold form kernelForm
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]

/-- The pre-Hilbert space of finitely supported families. -/
def Pre (_K : PositiveKernel ι) : Type _ := ι →₀ ℂ

instance : AddCommGroup K.Pre := inferInstanceAs (AddCommGroup (ι →₀ ℂ))
instance : Module ℂ K.Pre := inferInstanceAs (Module ℂ (ι →₀ ℂ))

/-- The identification of finitely supported families with the pre-Hilbert space. -/
def toPre : (ι →₀ ℂ) ≃ₗ[ℂ] K.Pre := LinearEquiv.refl ℂ _

/-- The semi-inner product of the pre-Hilbert space. -/
abbrev preCore : PreInnerProductSpace.Core ℂ K.Pre where
  inner f g := K.form (K.toPre.symm f) (K.toPre.symm g)
  conj_inner_symm _ _ := K.conj_form _ _
  re_inner_nonneg _ := K.re_form_self_nonneg _
  add_left _ _ _ := K.form_add_left _ _ _
  smul_left _ _ _ := K.form_smul_left _ _ _

instance : SeminormedAddCommGroup K.Pre :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := K.preCore)

instance : InnerProductSpace ℂ K.Pre := InnerProductSpace.ofCore K.preCore

theorem pre_inner_def (f g : K.Pre) : ⟪f, g⟫_ℂ = K.form (K.toPre.symm f) (K.toPre.symm g) := rfl

/-- The Hilbert space of the kernel. -/
abbrev Space := Completion K.Pre

/-- The vector of the index `i`. -/
def vec (i : ι) : K.Space := ((K.toPre (Finsupp.single i 1) : K.Pre) : K.Space)

theorem inner_vec_vec (i j : ι) : ⟪K.vec i, K.vec j⟫_ℂ = K i j := by
  simp only [vec, Completion.inner_coe, pre_inner_def, LinearEquiv.symm_apply_apply,
    form_single_single, map_one, one_mul]

theorem coe_toPre (f : ι →₀ ℂ) :
    ((K.toPre f : K.Pre) : K.Space) = f.sum fun i a => a • K.vec i := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, Completion.coe_add, hf, hg, Finsupp.sum_add_index' (fun i => by simp)
      (fun i a b => add_smul a b _)]
  | single i a =>
    rw [Finsupp.sum_single_index (by simp), vec, ← Completion.coe_smul, ← map_smul,
      Finsupp.smul_single, smul_eq_mul, mul_one]

theorem dense_span_vec : Dense (Submodule.span ℂ (Set.range K.vec) : Set K.Space) := by
  refine (Completion.denseRange_coe).mono ?_
  rintro _ ⟨f, rfl⟩
  have : ((K.toPre (K.toPre.symm f) : K.Pre) : K.Space) ∈ Submodule.span ℂ (Set.range K.vec) := by
    rw [coe_toPre]
    exact Submodule.finsuppSum_mem _ _ _ _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  simpa using this

/-- Two vectors with the same inner products against every `K.vec j` are equal. -/
theorem ext_inner_vec {u v : K.Space} (h : ∀ j, ⟪u, K.vec j⟫_ℂ = ⟪v, K.vec j⟫_ℂ) : u = v := by
  rw [← sub_eq_zero]
  have hzero : ∀ x ∈ Submodule.span ℂ (Set.range K.vec), ⟪u - v, x⟫_ℂ = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [inner_sub_left, h, sub_self]
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]
  have hcont : Continuous fun x : K.Space => ⟪u - v, x⟫_ℂ := continuous_const.inner continuous_id
  have hall : ∀ x : K.Space, ⟪u - v, x⟫_ℂ = 0 := by
    intro x
    have hcl : x ∈ closure (Submodule.span ℂ (Set.range K.vec) : Set K.Space) := by
      rw [K.dense_span_vec.closure_eq]; trivial
    exact (isClosed_eq hcont continuous_const).closure_subset_iff.mpr
      (fun y hy => hzero y hy) hcl
  exact inner_self_eq_zero.mp (hall _)

/-- Two continuous linear maps agreeing on every `K.vec i` are equal. -/
theorem clm_ext_vec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A B : K.Space →L[ℂ] E} (h : ∀ i, A (K.vec i) = B (K.vec i)) : A = B := by
  have hspan : ∀ x ∈ Submodule.span ℂ (Set.range K.vec), A x = B x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | smul a x _ hx => rw [map_smul, map_smul, hx]
  ext x
  have hcl : x ∈ closure (Submodule.span ℂ (Set.range K.vec) : Set K.Space) := by
    rw [K.dense_span_vec.closure_eq]; trivial
  exact (isClosed_eq A.continuous B.continuous).closure_subset_iff.mpr hspan hcl

/-! ### Operators induced by index maps -/

variable {ι' : Type*} (K' : PositiveKernel ι')

/-- The linear map of pre-Hilbert spaces induced by an index map. -/
def preMap (m : ι → ι') : K.Pre →ₗ[ℂ] K'.Pre :=
  K'.toPre.toLinearMap ∘ₗ Finsupp.lmapDomain ℂ ℂ m ∘ₗ K.toPre.symm.toLinearMap

theorem preMap_apply (m : ι → ι') (f : K.Pre) :
    K.preMap K' m f = K'.toPre (Finsupp.mapDomain m (K.toPre.symm f)) := rfl

theorem preMap_single (m : ι → ι') (i : ι) (a : ℂ) :
    K.preMap K' m (K.toPre (Finsupp.single i a)) = K'.toPre (Finsupp.single (m i) a) := by
  rw [preMap_apply, LinearEquiv.symm_apply_apply, Finsupp.mapDomain_single]

theorem form_mapDomain (m : ι → ι') (f g : ι →₀ ℂ) :
    K'.form (Finsupp.mapDomain m f) (Finsupp.mapDomain m g) =
      kernelForm (fun i j => K' (m i) (m j)) f g := by
  unfold form kernelForm
  rw [Finsupp.sum_mapDomain_index (fun i => by simp) (fun i a₁ a₂ => ?_)]
  · refine Finsupp.sum_congr (fun i _ => ?_)
    rw [Finsupp.sum_mapDomain_index (fun j => by simp) (fun j b₁ b₂ => by ring)]
  · rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr (fun j _ => ?_)
    simp only [map_add]
    ring

/-- A kernel-preserving index map induces a linear isometry of the pre-Hilbert spaces. -/
def preIsometry (m : ι → ι') (hm : ∀ i j, K' (m i) (m j) = K i j) : K.Pre →ₗᵢ[ℂ] K'.Pre where
  toLinearMap := K.preMap K' m
  norm_map' f := by
    have hinner : ⟪K.preMap K' m f, K.preMap K' m f⟫_ℂ = ⟪f, f⟫_ℂ := by
      simp only [preMap, pre_inner_def, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, LinearEquiv.symm_apply_apply, Finsupp.lmapDomain_apply]
      rw [form_mapDomain]
      simp only [hm]
      rfl
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), hinner]

/-- A kernel-preserving index map induces a linear isometry of the Hilbert spaces. -/
def isometryOfMap (m : ι → ι') (hm : ∀ i j, K' (m i) (m j) = K i j) :
    K.Space →ₗᵢ[ℂ] K'.Space where
  toLinearMap := (K.preIsometry K' m hm).toContinuousLinearMap.completion.toLinearMap
  norm_map' x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq
        ((K.preIsometry K' m hm).toContinuousLinearMap.completion.continuous.norm) continuous_norm
    | ih a =>
      simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.completion_apply_coe,
        Completion.norm_coe]
      exact (K.preIsometry K' m hm).norm_map a

theorem isometryOfMap_vec (m : ι → ι') (hm : ∀ i j, K' (m i) (m j) = K i j) (i : ι) :
    K.isometryOfMap K' m hm (K.vec i) = K'.vec (m i) := by
  change (K.preIsometry K' m hm).toContinuousLinearMap.completion _ = _
  rw [vec, vec, ContinuousLinearMap.completion_apply_coe]
  exact congrArg _ (K.preMap_single K' m i 1)

/-- For a real `C ≥ 0`, an index map `m` with
`Re (kernelForm (fun i j => K' (m i) (m j)) f f) ≤ C² Re (K.form f f)` for every finitely supported
`f` induces a bounded operator with `vec i ↦ vec (m i)` (`opOfMap_vec`) of norm at most `C`
(`opOfMap_norm_le`). -/
def opOfMap (m : ι → ι') (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ f : ι →₀ ℂ,
      (kernelForm (fun i j => K' (m i) (m j)) f f).re ≤ C ^ 2 * (K.form f f).re) :
    K.Space →L[ℂ] K'.Space :=
  ((K.preMap K' m).mkContinuous C fun f => by
    have h1 : ‖K.preMap K' m f‖ ^ 2 ≤ (C * ‖f‖) ^ 2 := by
      rw [mul_pow, norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
      simp only [preMap, pre_inner_def, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, LinearEquiv.symm_apply_apply, Finsupp.lmapDomain_apply]
      rw [form_mapDomain]
      exact hm _
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp h1).completion

theorem opOfMap_vec (m : ι → ι') (C : ℝ) (hC : 0 ≤ C) (hm) (i : ι) :
    K.opOfMap K' m C hC hm (K.vec i) = K'.vec (m i) := by
  rw [opOfMap, vec, vec, ContinuousLinearMap.completion_apply_coe, LinearMap.mkContinuous_apply]
  exact congrArg _ (K.preMap_single K' m i 1)

theorem opOfMap_norm_le (m : ι → ι') (C : ℝ) (hC : 0 ≤ C) (hm) :
    ‖K.opOfMap K' m C hC hm‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_le (K.opOfMap K' m C hC hm).continuous.norm
      (continuous_const.mul continuous_norm)
  | ih a =>
    rw [opOfMap, ContinuousLinearMap.completion_apply_coe, Completion.norm_coe,
      Completion.norm_coe]
    exact (ContinuousLinearMap.le_opNorm _ a).trans (mul_le_mul_of_nonneg_right
      (LinearMap.mkContinuous_norm_le _ hC _) (norm_nonneg a))

end PositiveKernel

end Langlands.Analysis
