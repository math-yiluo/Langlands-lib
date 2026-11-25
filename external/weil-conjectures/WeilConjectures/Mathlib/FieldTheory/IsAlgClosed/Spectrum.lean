/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenvalues of powers and of quotients of endomorphisms

- `Module.End.HasEigenvalue.of_surjective_comp_eq`: if a surjective linear map `r` intertwines
  `f` and `g`, every eigenvalue of `g` is an eigenvalue of `f`.
- `Module.End.HasEigenvalue.exists_pow_eq`: over an algebraically closed field, every eigenvalue
  of `f ^ n`, `n > 0`, is the `n`-th power of an eigenvalue of `f`.
-/

@[expose] public section

namespace Module.End

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- If a surjective linear map `r : V → W` intertwines `f` and `g` (`r ∘ f = g ∘ r`), every
eigenvalue of `g` is an eigenvalue of `f`: if `μ - f` were bijective, so would be `μ - g`. -/
theorem HasEigenvalue.of_surjective_comp_eq [FiniteDimensional K V] [FiniteDimensional K W]
    {f : End K V} {g : End K W} {r : V →ₗ[K] W} (hr : Function.Surjective r)
    (hfg : r ∘ₗ f = g ∘ₗ r) {μ : K} (hμ : g.HasEigenvalue μ) : f.HasEigenvalue μ := by
  rw [hasEigenvalue_iff_mem_spectrum, spectrum.mem_iff] at hμ ⊢
  intro hf
  suffices hs : Function.Surjective (algebraMap K (End K W) μ - g) from
    hμ ((isUnit_iff _).2 ⟨LinearMap.injective_iff_surjective.2 hs, hs⟩)
  intro w
  obtain ⟨v, rfl⟩ := hr w
  obtain ⟨u, rfl⟩ := ((isUnit_iff _).1 hf).2 v
  refine ⟨r u, ?_⟩
  have h := LinearMap.congr_fun hfg u
  simp only [LinearMap.coe_comp, Function.comp_apply] at h
  simp [algebraMap_end_apply, h]

/-- Over an algebraically closed field, every eigenvalue of `f ^ n`, `n > 0`, is the `n`-th
power of an eigenvalue of `f` (spectral mapping theorem). -/
theorem HasEigenvalue.exists_pow_eq [IsAlgClosed K] [FiniteDimensional K V] {f : End K V}
    {n : ℕ} (hn : 0 < n) {μ : K} (h : (f ^ n).HasEigenvalue μ) :
    ∃ α, f.HasEigenvalue α ∧ α ^ n = μ := by
  rw [hasEigenvalue_iff_mem_spectrum, spectrum.map_pow_of_pos _ hn] at h
  obtain ⟨α, hα, rfl⟩ := h
  exact ⟨α, hasEigenvalue_iff_mem_spectrum.2 hα, rfl⟩

end Module.End
