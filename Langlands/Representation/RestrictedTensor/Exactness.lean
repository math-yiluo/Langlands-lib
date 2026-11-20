import Langlands.Representation.RestrictedTensor.Maps
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Injective and surjective maps of algebraic restricted tensor products -/

noncomputable section

universe uK uI uV uW

namespace Langlands.RestrictedTensor

variable {K : Type uK} [Field K] {ι : Type uI}
variable {V : ι → Type uV} {W : ι → Type uW}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

/-- A reference-preserving family of injections gives an injection on the restricted tensor. -/
theorem map_injective_of_injective (E E' : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (f : ∀ i, V i →ₗ[K] W i) (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i)
    (hinj : ∀ i, Function.Injective (f i)) : Function.Injective (map E E' e e' f hf) := by
  classical
  choose g hg using fun i =>
    (f i).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (hinj i))
  have hg_apply (i : ι) (x : V i) : g i (f i x) = x := LinearMap.congr_fun (hg i) x
  have hg_ref : ∀ᶠ i in Filter.cofinite, g i (e' i) = e i :=
    hf.mono fun i hi => hi ▸ hg_apply i (e i)
  have hleft : (map E' E e' e g hg_ref).comp (map E E' e e' f hf) = LinearMap.id := by
    rw [map_comp]
    simpa only [hg] using map_id (K := K) E e
  have h : Function.LeftInverse (map E' E e' e g hg_ref) (map E E' e e' f hf) := by
    intro x
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using LinearMap.congr_fun hleft x
  exact h.injective

/-- A reference-preserving family of surjections gives a surjection on the restricted tensor. -/
theorem map_surjective_of_surjective (E E' : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (f : ∀ i, V i →ₗ[K] W i) (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i)
    (hsurj : ∀ i, Function.Surjective (f i)) : Function.Surjective (map E E' e e' f hf) := by
  classical
  intro y
  obtain ⟨S, z, rfl⟩ := exists_of E' e' y
  refine PiTensorProduct.induction_on z ?_ ?_
  · intro a w
    let U : Index E := ⟨S.1 ∪ (E ∪ mapBound E' hf),
      (Finset.subset_union_left : E ⊆ E ∪ mapBound E' hf).trans Finset.subset_union_right⟩
    have hS : S.1 ⊆ U.1 := Finset.subset_union_left
    have hU : mapBound E' hf ⊆ U.1 := Finset.subset_union_right.trans Finset.subset_union_right
    choose v hv using fun i : U.1 => hsurj i (extend e' w i)
    refine ⟨a • pure E e U v, ?_⟩
    simp only [map_smul, map_pure_of_subset _ _ _ _ _ _ _ hU, hv]
    rw [pure_extend E' e' (S := S) (T := ⟨U.1, (subset_mapBound E' hf).trans hU⟩) hS]
    rfl
  · intro z₁ z₂ hz₁ hz₂
    obtain ⟨x₁, hx₁⟩ := hz₁
    obtain ⟨x₂, hx₂⟩ := hz₂
    exact ⟨x₁ + x₂, by rw [map_add, hx₁, hx₂, map_add]⟩

end Langlands.RestrictedTensor
