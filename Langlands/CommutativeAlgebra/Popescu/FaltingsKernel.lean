import Langlands.CommutativeAlgebra.Popescu.FaltingsSquare

/-! # Kernels after base change, and the kernel of `K' ⊗ Ω_A → K' ⊗ Ω_{A'}` -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace Faltings

open IsLocalRing

open scoped TensorProduct

/-- If `M → N → P → 0` is exact with `P` projective, then the kernel of `Q ⊗ M → Q ⊗ N` is the
image of `Q ⊗ ker(M → N)`. -/
theorem ker_lTensor_eq_range {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [Module.Projective R P]
    (φ : M →ₗ[R] N) (ψ : N →ₗ[R] P) (hex : Function.Exact φ ψ) (hψ : Function.Surjective ψ)
    (Q : Type*) [AddCommGroup Q] [Module R Q] :
    LinearMap.ker (φ.lTensor Q) = LinearMap.range ((LinearMap.ker φ).subtype.lTensor Q) := by
  apply le_antisymm
  · obtain ⟨s, hs⟩ := Module.projective_lifting_property ψ LinearMap.id hψ
    have hmem : ∀ x : N, x - s (ψ x) ∈ LinearMap.range φ := by
      intro x
      rw [← hex.linearMap_ker_eq, LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply ψ s, hs,
        LinearMap.id_apply, sub_self]
    let r : N →ₗ[R] LinearMap.range φ :=
      LinearMap.codRestrict (LinearMap.range φ) (LinearMap.id - s ∘ₗ ψ) hmem
    have hr : r ∘ₗ (LinearMap.range φ).subtype = LinearMap.id := by
      ext ⟨_, ⟨m, rfl⟩⟩
      simp [r, hex.apply_apply_eq_zero m]
    have hinj : Function.Injective ((LinearMap.range φ).subtype.lTensor Q) := by
      intro x y hxy
      have := congrArg (r.lTensor Q) hxy
      rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hr,
        LinearMap.lTensor_id, LinearMap.id_apply, LinearMap.id_apply] at this
    intro w hw
    have hfac : φ.lTensor Q = (LinearMap.range φ).subtype.lTensor Q ∘ₗ φ.rangeRestrict.lTensor Q := by
      rw [← LinearMap.lTensor_comp]
      rfl
    have hw' : φ.rangeRestrict.lTensor Q w = 0 := by
      apply hinj
      rw [map_zero, ← LinearMap.comp_apply, ← hfac]
      exact hw
    have hexr : Function.Exact (LinearMap.ker φ.rangeRestrict).subtype φ.rangeRestrict :=
      LinearMap.exact_subtype_ker_map _
    have := (lTensor_exact Q hexr φ.surjective_rangeRestrict w).mp hw'
    rwa [LinearMap.ker_rangeRestrict] at this
  · rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have : φ ∘ₗ (LinearMap.ker φ).subtype = 0 := by
      ext ⟨m, hm⟩
      exact hm
    rw [this, LinearMap.lTensor_zero, LinearMap.zero_apply]

end Faltings

end Langlands.CommutativeAlgebra.Popescu
