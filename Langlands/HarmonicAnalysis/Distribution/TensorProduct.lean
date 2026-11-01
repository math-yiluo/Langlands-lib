import Langlands.HarmonicAnalysis.Distribution.Basic
import Langlands.HarmonicAnalysis.SchwartzBruhatProduct
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Algebraic tensor maps and tensor products of distributions -/

noncomputable section

open scoped TensorProduct

namespace Langlands.HarmonicAnalysis

universe uX uY

variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]

namespace SchwartzBruhat

/-- Bilinear packaging of the existing scalar external product. -/
def tensorBilinear : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Y →ₗ[ℂ]
    SchwartzBruhat (X × Y) where
  toFun f :=
    { toFun := tensor f
      map_add' := by
        intro g h
        ext z
        exact mul_add _ _ _
      map_smul' := by
        intro c g
        ext z
        exact mul_left_comm _ _ _ }
  map_add' := by
    intro f g
    ext h z
    exact add_mul _ _ _
  map_smul' := by
    intro c f
    ext g z
    exact mul_assoc _ _ _

/-- Canonical algebraic tensor map for scalar test functions. -/
def tensorLinearMap : SchwartzBruhat X ⊗[ℂ] SchwartzBruhat Y →ₗ[ℂ]
    SchwartzBruhat (X × Y) :=
  TensorProduct.lift tensorBilinear

@[simp] theorem tensorLinearMap_tmul (f : SchwartzBruhat X) (g : SchwartzBruhat Y) :
    tensorLinearMap (f ⊗ₜ[ℂ] g) = tensor f g := rfl

@[simp] theorem tensorLinearMap_tmul_apply (f : SchwartzBruhat X)
    (g : SchwartzBruhat Y) (x : X) (y : Y) :
    tensorLinearMap (f ⊗ₜ[ℂ] g) (x, y) = f x * g y := rfl

/-- The slice at a fixed second coordinate, with the original induced function. -/
def sliceFst [T2Space X] (f : SchwartzBruhat (X × Y)) (y : Y) : SchwartzBruhat X :=
  compLeftInverse f (fun x => (x, y)) Prod.fst (continuous_id.prodMk continuous_const)
    continuous_fst (fun _ => rfl)

@[simp] theorem sliceFst_apply [T2Space X] (f : SchwartzBruhat (X × Y))
    (x : X) (y : Y) : sliceFst f y x = f (x, y) := rfl

@[simp] theorem sliceSnd_add [T2Space Y] (f g : SchwartzBruhat (X × Y)) (x : X) :
    sliceSnd (f + g) x = sliceSnd f x + sliceSnd g x := by
  ext y
  rfl

@[simp] theorem sliceSnd_smul [T2Space Y] (c : ℂ) (f : SchwartzBruhat (X × Y)) (x : X) :
    sliceSnd (c • f) x = c • sliceSnd f x := by
  ext y
  rfl

@[simp] theorem sliceFst_add [T2Space X] (f g : SchwartzBruhat (X × Y)) (y : Y) :
    sliceFst (f + g) y = sliceFst f y + sliceFst g y := by
  ext x
  rfl

@[simp] theorem sliceFst_smul [T2Space X] (c : ℂ) (f : SchwartzBruhat (X × Y)) (y : Y) :
    sliceFst (c • f) y = c • sliceFst f y := by
  ext x
  rfl

end SchwartzBruhat

namespace Distribution

variable [T2Space X] [T2Space Y]

private theorem partialApplySnd_mem (S : Distribution Y) (f : SchwartzBruhat (X × Y)) :
    (fun x => S (SchwartzBruhat.sliceSnd f x)) ∈ schwartzBruhatSubmodule X := by
  obtain ⟨n, a, b, hf⟩ := SchwartzBruhat.exists_tensor_expansion f
  have hs (x : X) : SchwartzBruhat.sliceSnd f x = ∑ j, (a j x) • b j := by
    ext y
    simpa using hf x y
  have he : (fun x => S (SchwartzBruhat.sliceSnd f x)) =
      ∑ j, S (b j) • (a j : X → ℂ) := by
    funext x
    rw [hs]
    simp [mul_comm]
  rw [he]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (a j).property

/-- Apply a distribution in the second variable to obtain an actual test on X. -/
def partialApplySnd (S : Distribution Y) : SchwartzBruhat (X × Y) →ₗ[ℂ]
    SchwartzBruhat X where
  toFun f := ⟨fun x => S (SchwartzBruhat.sliceSnd f x), partialApplySnd_mem S f⟩
  map_add' := by
    intro f g
    ext x
    simp only [SchwartzBruhat.sliceSnd_add, map_add]
    rfl
  map_smul' := by
    intro c f
    ext x
    simp only [SchwartzBruhat.sliceSnd_smul, map_smul]
    rfl

@[simp] theorem partialApplySnd_apply (S : Distribution Y) (f : SchwartzBruhat (X × Y))
    (x : X) : partialApplySnd S f x = S (SchwartzBruhat.sliceSnd f x) := rfl

private theorem partialApplyFst_mem (T : Distribution X) (f : SchwartzBruhat (X × Y)) :
    (fun y => T (SchwartzBruhat.sliceFst f y)) ∈ schwartzBruhatSubmodule Y := by
  obtain ⟨n, a, b, hf⟩ := SchwartzBruhat.exists_tensor_expansion f
  have hs (y : Y) : SchwartzBruhat.sliceFst f y = ∑ j, (b j y) • a j := by
    ext x
    simpa [mul_comm] using hf x y
  have he : (fun y => T (SchwartzBruhat.sliceFst f y)) =
      ∑ j, T (a j) • (b j : Y → ℂ) := by
    funext y
    rw [hs]
    simp [mul_comm]
  rw [he]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).property

/-- Apply a distribution in the first variable to obtain an actual test on Y. -/
def partialApplyFst (T : Distribution X) : SchwartzBruhat (X × Y) →ₗ[ℂ]
    SchwartzBruhat Y where
  toFun f := ⟨fun y => T (SchwartzBruhat.sliceFst f y), partialApplyFst_mem T f⟩
  map_add' := by
    intro f g
    ext y
    simp only [SchwartzBruhat.sliceFst_add, map_add]
    rfl
  map_smul' := by
    intro c f
    ext y
    simp only [SchwartzBruhat.sliceFst_smul, map_smul]
    rfl

@[simp] theorem partialApplyFst_apply (T : Distribution X) (f : SchwartzBruhat (X × Y))
    (y : Y) : partialApplyFst T f y = T (SchwartzBruhat.sliceFst f y) := rfl

@[simp] theorem partialApplySnd_tensor (S : Distribution Y)
    (f : SchwartzBruhat X) (g : SchwartzBruhat Y) :
    partialApplySnd S (SchwartzBruhat.tensor f g) = S g • f := by
  ext x
  have hs : SchwartzBruhat.sliceSnd (SchwartzBruhat.tensor f g) x = f x • g := by
    ext y
    rfl
  simp [hs, mul_comm]

@[simp] theorem partialApplyFst_tensor (T : Distribution X)
    (f : SchwartzBruhat X) (g : SchwartzBruhat Y) :
    partialApplyFst T (SchwartzBruhat.tensor f g) = T f • g := by
  ext y
  have hs : SchwartzBruhat.sliceFst (SchwartzBruhat.tensor f g) y = g y • f := by
    ext x
    exact mul_comm _ _
  simp [hs, mul_comm]

/-- Tensor product of full algebraic distributions, by actual partial evaluation. -/
def tensor (T : Distribution X) (S : Distribution Y) : Distribution (X × Y) :=
  T.comp (partialApplySnd S)

@[simp] theorem tensor_apply (T : Distribution X) (S : Distribution Y)
    (f : SchwartzBruhat (X × Y)) : tensor T S f = T (partialApplySnd S f) := rfl

@[simp] theorem tensor_apply_tensor (T : Distribution X) (S : Distribution Y)
    (f : SchwartzBruhat X) (g : SchwartzBruhat Y) :
    tensor T S (SchwartzBruhat.tensor f g) = T f * S g := by
  simp [mul_comm]

/-- Full complex bilinearity of the distribution tensor product. -/
def tensorBilinear : Distribution X →ₗ[ℂ] Distribution Y →ₗ[ℂ]
    Distribution (X × Y) where
  toFun T :=
    { toFun := tensor T
      map_add' := by
        intro S R
        ext f
        change T (partialApplySnd (S + R) f) = _
        have h : partialApplySnd (S + R) f = partialApplySnd S f + partialApplySnd R f := by
          ext x
          rfl
        rw [h, map_add]
        rfl
      map_smul' := by
        intro c S
        ext f
        change T (partialApplySnd (c • S) f) = _
        have h : partialApplySnd (c • S) f = c • partialApplySnd S f := by
          ext x
          rfl
        rw [h, map_smul]
        rfl }
  map_add' := by
    intro T R
    ext S f
    rfl
  map_smul' := by
    intro c T
    ext S f
    rfl

@[simp] theorem tensorBilinear_apply (T : Distribution X) (S : Distribution Y) :
    tensorBilinear T S = tensor T S := rfl

theorem tensor_add_left (T R : Distribution X) (S : Distribution Y) :
    tensor (T + R) S = tensor T S + tensor R S :=
  LinearMap.congr_fun (tensorBilinear.map_add T R) S

theorem tensor_smul_left (c : ℂ) (T : Distribution X) (S : Distribution Y) :
    tensor (c • T) S = c • tensor T S :=
  LinearMap.congr_fun (tensorBilinear.map_smul c T) S

theorem tensor_add_right (T : Distribution X) (S R : Distribution Y) :
    tensor T (S + R) = tensor T S + tensor T R :=
  (tensorBilinear T).map_add S R

theorem tensor_smul_right (c : ℂ) (T : Distribution X) (S : Distribution Y) :
    tensor T (c • S) = c • tensor T S :=
  (tensorBilinear T).map_smul c S

end Distribution
end Langlands.HarmonicAnalysis
