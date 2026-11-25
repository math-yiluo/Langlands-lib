/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Trace
public import WeilConjectures.Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Additivity and multiplicativity of the trace

For a short exact sequence `0 → M → N → P → 0` of modules over a commutative ring with `M` and
`P` finite free, and endomorphisms `φM`, `φN`, `φP` compatible with the maps,
`tr φN = tr φM + tr φP` (`LinearMap.trace_eq_trace_add_trace_of_exact`). This is the linear
algebra behind blueprint `proposition-properties-trace`, items (2) and (4).

For endomorphisms `g` of `N` and `h` of `M` (free of finite rank), the endomorphism
`f ↦ g ∘ f ∘ h` of `M →ₗ N` has trace `tr(g) tr(h)`
(`LinearMap.trace_compLeft_compRight`). Consequently, if a perfect pairing `V × M → N`
intertwines endomorphisms `F_V`, an automorphism `F_M` and `F_N`, then
`tr(F_V) = tr(F_N) tr(F_M⁻¹)` (`LinearMap.trace_eq_mul_of_bijective`).
-/

@[expose] public section

open TensorProduct

namespace LinearMap

section Exact

variable {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup P] [Module R P]

/-- The trace of an endomorphism of a subsingleton module is zero. -/
lemma trace_eq_zero_of_subsingleton [Subsingleton M] (φ : M →ₗ[R] M) : trace R M φ = 0 := by
  rw [Subsingleton.elim φ 0, map_zero]

/-- **Additivity of the trace on short exact sequences**: for a short exact sequence
`0 → M → N → P → 0` of modules with `M`, `P` finite free (hence also `N`) and endomorphisms
`φM`, `φN`, `φP` commuting with the maps, `tr φN = tr φM + tr φP`. The sequence splits since `P`
is projective, and with a splitting `id = f ∘ r + s ∘ g` the claim follows from the cyclicity of
the trace. -/
theorem trace_eq_trace_add_trace_of_exact [Module.Free R M] [Module.Finite R M] [Module.Free R P]
    [Module.Finite R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P} (hfg : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) {φM : M →ₗ[R] M} {φN : N →ₗ[R] N}
    {φP : P →ₗ[R] P} (hM : φN ∘ₗ f = f ∘ₗ φM) (hP : g ∘ₗ φN = φP ∘ₗ g) :
    trace R N φN = trace R M φM + trace R P φP := by
  have := Module.Free.of_exact hfg hf hg
  have := Module.Finite.of_exact hfg hg
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id hg
  obtain ⟨e, hef, heg⟩ := hfg.splitSurjectiveEquiv hf ⟨l, hl⟩
  set r := fst R M P ∘ₗ e.toLinearMap
  set s := e.symm.toLinearMap ∘ₗ inr R M P
  have hrf : r ∘ₗ f = LinearMap.id := by
    rw [hef]
    ext
    simp [r]
  have hgs : g ∘ₗ s = LinearMap.id := by
    rw [heg]
    ext
    simp [s]
  have hid : f ∘ₗ r + s ∘ₗ g = LinearMap.id := by
    rw [hef, heg]
    ext x
    simp only [add_apply, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, coe_inl, coe_fst,
      coe_inr, coe_snd, id_coe, id_eq, r, s]
    rw [← map_add, Prod.fst_add_snd, LinearEquiv.symm_apply_apply]
  calc trace R N φN = trace R N ((φN ∘ₗ f) ∘ₗ r) + trace R N ((φN ∘ₗ s) ∘ₗ g) := by
        rw [← map_add, comp_assoc, comp_assoc, ← comp_add, hid, comp_id]
    _ = trace R M (r ∘ₗ φN ∘ₗ f) + trace R P (g ∘ₗ φN ∘ₗ s) := by
        rw [trace_comp_comm' (φN ∘ₗ f) r, trace_comp_comm' (φN ∘ₗ s) g]
    _ = trace R M φM + trace R P φP := by
        rw [hM, ← comp_assoc, ← comp_assoc, hP, hrf, comp_assoc, hgs, id_comp,
          comp_id]

end Exact

section Pairing

variable {R M N V : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M] [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
  [AddCommGroup V] [Module R V]

/-- The trace of the endomorphism `f ↦ g ∘ f ∘ h` of `M →ₗ N` is `tr(g) tr(h)`: under the
identification `M^∨ ⊗ N ≅ (M →ₗ N)` it is `hᵀ ⊗ g`. -/
theorem trace_compLeft_compRight (g : N →ₗ[R] N) (h : M →ₗ[R] M) :
    trace R (M →ₗ[R] N) ((llcomp R M N N g) ∘ₗ (llcomp R M M N).flip h) =
      trace R N g * trace R M h := by
  have h₁ : (dualTensorHomEquiv R M N).toLinearMap ∘ₗ map (Module.Dual.transpose (R := R) h) g =
      ((llcomp R M N N g) ∘ₗ (llcomp R M M N).flip h) ∘ₗ
        (dualTensorHomEquiv R M N).toLinearMap := by
    refine TensorProduct.ext' fun f n ↦ LinearMap.ext fun m ↦ ?_
    simp [Module.Dual.transpose_apply, dualTensorHom_apply]
  have hc : (dualTensorHomEquiv R M N).conj (map (Module.Dual.transpose (R := R) h) g) =
      (llcomp R M N N g) ∘ₗ (llcomp R M M N).flip h := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨y, rfl⟩ := (dualTensorHomEquiv R M N).surjective x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun h₁ y
  rw [← hc, trace_conj', trace_tensorProduct', trace_transpose', mul_comm]

/-- If a perfect pairing `p : V × M → N` intertwines endomorphisms `F_V` of `V` and `F_N` of `N`
with an automorphism `F_M` of `M`, `p (F_V v) (F_M m) = F_N (p v m)`, then
`tr(F_V) = tr(F_N) tr(F_M⁻¹)`: under `V ≅ (M →ₗ N)`, `F_V` is `f ↦ F_N ∘ f ∘ F_M⁻¹`. -/
theorem trace_eq_mul_of_bijective (p : V →ₗ[R] M →ₗ[R] N) (hp : Function.Bijective p)
    (fV : V →ₗ[R] V) (fM : M ≃ₗ[R] M) (fN : N →ₗ[R] N)
    (h : ∀ v m, p (fV v) (fM m) = fN (p v m)) :
    trace R V fV = trace R N fN * trace R M fM.symm.toLinearMap := by
  let e := LinearEquiv.ofBijective p hp
  have hc : e.conj fV = (llcomp R M N N fN) ∘ₗ (llcomp R M M N).flip fM.symm.toLinearMap := by
    refine LinearMap.ext fun f ↦ LinearMap.ext fun m ↦ ?_
    obtain ⟨v, rfl⟩ := e.surjective f
    have := h v (fM.symm m)
    simp only [LinearEquiv.apply_symm_apply] at this
    simp [LinearEquiv.conj_apply, e, this]
  rw [← trace_compLeft_compRight, ← hc, trace_conj']

/-- The trace of the operator `φ ↦ g ∘ φ ∘ h` on `M →ₗ[R] N` is `tr g * tr h`. -/
theorem trace_llcomp_comp_lcomp (g : N →ₗ[R] N) (h : M →ₗ[R] M) :
    trace R (M →ₗ[R] N) (llcomp R M N N g ∘ₗ lcomp R N h) = trace R N g * trace R M h :=
  trace_compLeft_compRight g h

end Pairing

end LinearMap
