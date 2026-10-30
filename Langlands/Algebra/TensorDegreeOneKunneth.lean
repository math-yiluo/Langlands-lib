import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# A degree-one Künneth lemma for tensor products over a field

Let `C₀ ⟶ C₁` and `D₀ ⟶ D₁` be linear maps of vector spaces over a field `K` whose kernels are
the lines spanned by `eC` and `eD`, and let `εC`, `εD` be linear forms with `εC eC = 1` and
`εD eD = 1`. Given `h ∈ C₁ ⊗ D₀` and `v ∈ C₀ ⊗ D₁` with `(1 ⊗ dD) h = (dC ⊗ 1) v`, whose images
`(1 ⊗ εD) h ∈ C₁` and `(εC ⊗ 1) v ∈ D₁` are boundaries, there is `w ∈ C₀ ⊗ D₀` with
`(dC ⊗ 1) w = h` and `(1 ⊗ dD) w = v`.

This is the degree-one part of the Künneth formula for the tensor product of two two-term
complexes over a field, in the form used for Čech cochains of a product.
-/

open TensorProduct LinearMap

namespace Langlands.Algebra.TensorDegreeOneKunneth

variable {K : Type*} [Field K]
variable {C₀ C₁ D₀ D₁ : Type*} [AddCommGroup C₀] [Module K C₀] [AddCommGroup C₁] [Module K C₁]
  [AddCommGroup D₀] [Module K D₀] [AddCommGroup D₁] [Module K D₁]

lemma rTensor_lTensor_comm {M N P Q : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N]
    [Module K N] [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
    (f : M →ₗ[K] P) (g : N →ₗ[K] Q) (t : M ⊗[K] N) :
    f.rTensor Q (g.lTensor M t) = g.lTensor P (f.rTensor N t) := by
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
    LinearMap.comp_apply]

lemma lid_rTensor_lTensor {M N P : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N]
    [Module K N] [AddCommGroup P] [Module K P] (ε : M →ₗ[K] K) (q : N →ₗ[K] P) (t : M ⊗[K] N) :
    TensorProduct.lid K P (ε.rTensor P (q.lTensor M t)) =
      q (TensorProduct.lid K N (ε.rTensor N t)) := by
  induction t with
  | tmul m n => simp
  | add a b ha hb => simp only [map_add, ha, hb]

lemma rid_lTensor_rTensor {M N P : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N]
    [Module K N] [AddCommGroup P] [Module K P] (ε : N →ₗ[K] K) (f : M →ₗ[K] P) (t : M ⊗[K] N) :
    TensorProduct.rid K P (ε.lTensor P (f.rTensor N t)) =
      f (TensorProduct.rid K M (ε.lTensor M t)) := by
  induction t with
  | tmul m n => simp
  | add a b ha hb => simp only [map_add, ha, hb]

/-- If the kernel of `d : D₀ ⟶ D₁` is spanned by `e`, every element of `M ⊗ D₀` killed by
`1 ⊗ d` has the form `γ ⊗ e`. -/
lemma exists_eq_tmul_of_lTensor_eq_zero (M : Type*) [AddCommGroup M] [Module K M]
    (d : D₀ →ₗ[K] D₁) (e : D₀) (he : ∀ x, d x = 0 → ∃ a : K, x = a • e) (t : M ⊗[K] D₀)
    (ht : d.lTensor M t = 0) : ∃ γ : M, t = γ ⊗ₜ e := by
  obtain ⟨s, rfl⟩ := (Module.Flat.lTensor_exact M (LinearMap.exact_subtype_ker_map d) t).1 ht
  clear ht
  induction s with
  | tmul m x =>
    obtain ⟨a, ha⟩ := he x x.2
    refine ⟨a • m, ?_⟩
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, ha, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  | add a b ha hb =>
    obtain ⟨γa, hγa⟩ := ha
    obtain ⟨γb, hγb⟩ := hb
    exact ⟨γa + γb, by rw [map_add, hγa, hγb, TensorProduct.add_tmul]⟩

/-- If the kernel of `d : C₀ ⟶ C₁` is spanned by `e`, every element of `C₀ ⊗ N` killed by
`d ⊗ 1` has the form `e ⊗ η`. -/
lemma exists_eq_tmul_of_rTensor_eq_zero (N : Type*) [AddCommGroup N] [Module K N]
    (d : C₀ →ₗ[K] C₁) (e : C₀) (he : ∀ x, d x = 0 → ∃ a : K, x = a • e) (t : C₀ ⊗[K] N)
    (ht : d.rTensor N t = 0) : ∃ η : N, t = e ⊗ₜ η := by
  obtain ⟨s, rfl⟩ := (Module.Flat.rTensor_exact N (LinearMap.exact_subtype_ker_map d) t).1 ht
  clear ht
  induction s with
  | tmul x n =>
    obtain ⟨a, ha⟩ := he x x.2
    refine ⟨a • n, ?_⟩
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, ha, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  | add a b ha hb =>
    obtain ⟨ηa, hηa⟩ := ha
    obtain ⟨ηb, hηb⟩ := hb
    exact ⟨ηa + ηb, by rw [map_add, hηa, hηb, TensorProduct.tmul_add]⟩

/-- Degree-one Künneth over a field: a mixed `1`-cocycle `(h, v)` of the tensor product of
`C₀ ⟶ C₁` and `D₀ ⟶ D₁` whose two "axis restrictions" are boundaries is a coboundary. -/
theorem exists_eq_of_degreeOne (dC : C₀ →ₗ[K] C₁) (dD : D₀ →ₗ[K] D₁) (eC : C₀) (eD : D₀)
    (εC : C₀ →ₗ[K] K) (εD : D₀ →ₗ[K] K)
    (hC : ∀ x, dC x = 0 → ∃ a : K, x = a • eC)
    (hD : ∀ x, dD x = 0 → ∃ a : K, x = a • eD) (hdD : dD eD = 0)
    (hεC : εC eC = 1) (hεD : εD eD = 1)
    (h : C₁ ⊗[K] D₀) (v : C₀ ⊗[K] D₁)
    (hhv : dD.lTensor C₁ h = dC.rTensor D₁ v)
    (hv : TensorProduct.lid K D₁ (εC.rTensor D₁ v) ∈ LinearMap.range dD)
    (hh : TensorProduct.rid K C₁ (εD.lTensor C₁ h) ∈ LinearMap.range dC) :
    ∃ w : C₀ ⊗[K] D₀, dC.rTensor D₀ w = h ∧ dD.lTensor C₀ w = v := by
  -- Step 1: `v` is in the image of `1 ⊗ dD`.
  let q := (LinearMap.range dD).mkQ
  have hq : dC.rTensor _ (q.lTensor C₀ v) = 0 := by
    rw [rTensor_lTensor_comm, ← hhv, ← LinearMap.comp_apply (q.lTensor C₁),
      ← LinearMap.lTensor_comp, LinearMap.range_mkQ_comp, LinearMap.lTensor_zero,
      LinearMap.zero_apply]
  obtain ⟨η, hη⟩ := exists_eq_tmul_of_rTensor_eq_zero _ dC eC hC _ hq
  have hη0 : η = 0 := by
    have h₁ := congrArg (fun t => TensorProduct.lid K _ (εC.rTensor _ t)) hη
    simp only [lid_rTensor_lTensor, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hεC,
      one_smul] at h₁
    rw [← h₁]
    exact (Submodule.Quotient.mk_eq_zero _).2 hv
  rw [hη0, TensorProduct.tmul_zero] at hη
  obtain ⟨w₀, hw₀⟩ :=
    (_root_.lTensor_exact C₀ (LinearMap.exact_map_mkQ_range dD) (Submodule.mkQ_surjective _) v).1
      hη
  -- Step 2: correct `w₀` by an element `α ⊗ eD`.
  have hh' : dD.lTensor C₁ (h - dC.rTensor D₀ w₀) = 0 := by
    rw [map_sub, hhv, ← rTensor_lTensor_comm, hw₀, sub_self]
  obtain ⟨γ, hγ⟩ := exists_eq_tmul_of_lTensor_eq_zero C₁ dD eD hD _ hh'
  obtain ⟨c, hc⟩ := hh
  have hγc : γ = dC (c - TensorProduct.rid K C₀ (εD.lTensor C₀ w₀)) := by
    have h₁ := congrArg (fun t => TensorProduct.rid K C₁ (εD.lTensor C₁ t)) hγ
    simp only [map_sub, rid_lTensor_rTensor, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
      hεD, one_smul] at h₁
    rw [map_sub, hc, ← h₁]
  refine ⟨w₀ + (c - TensorProduct.rid K C₀ (εD.lTensor C₀ w₀)) ⊗ₜ eD, ?_, ?_⟩
  · rw [map_add, LinearMap.rTensor_tmul, ← hγc, ← hγ, add_sub_cancel]
  · rw [map_add, LinearMap.lTensor_tmul, hdD, TensorProduct.tmul_zero, add_zero, hw₀]

end Langlands.Algebra.TensorDegreeOneKunneth
