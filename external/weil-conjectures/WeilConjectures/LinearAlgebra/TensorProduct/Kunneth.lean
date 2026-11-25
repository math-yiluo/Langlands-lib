/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Basic

/-!
# A Künneth argument in degree one

Let `C_X` and `C_Y` be the first two terms of two Čech-type complexes of vector spaces over a
field `k`, given by families of vector spaces `F₀ a`, `F₁ a a'` (resp. `G₀ b`, `G₁ b b'`) and
restriction maps, such that the differentials in degree zero are injective. A cochain of degree
one of the "product" complex, with components in `F₁ a a' ⊗ G₀ b` (horizontal) and
`F₀ a ⊗ G₁ b b'` (vertical), satisfying the cocycle relation, is a coboundary.

This is the degree one case of the Künneth formula `H¹(C_X ⊗ C_Y) = H⁰ ⊗ H¹ ⊕ H¹ ⊗ H⁰` when
`H⁰(C_X) = H⁰(C_Y) = 0`.

## Main statements

- `TensorProduct.exists_eq_rTensor_sub_and_eq_lTensor_sub`
-/

@[expose] public section

open TensorProduct

namespace TensorProduct

universe u

variable {k : Type u} [Field k] {α β : Type u} [Finite α] [Finite β] {F₀ : α → Type u}
  {F₁ : α → α → Type u} {G₀ : β → Type u} {G₁ : β → β → Type u}
  [∀ a, AddCommGroup (F₀ a)] [∀ a, Module k (F₀ a)] [∀ a a', AddCommGroup (F₁ a a')]
  [∀ a a', Module k (F₁ a a')] [∀ b, AddCommGroup (G₀ b)] [∀ b, Module k (G₀ b)]
  [∀ b b', AddCommGroup (G₁ b b')] [∀ b b', Module k (G₁ b b')]

/-- **A Künneth argument in degree one.** Let `fl a a' : F₀ a → F₁ a a'` and
`fr a a' : F₀ a' → F₁ a a'` be the two restriction maps of a Čech-type complex `C_X` over a
field, and similarly `gl`, `gr` for `C_Y`, and suppose that both differentials
`(f a)_a ↦ (fr (f a') - fl (f a))_{a a'}` in degree zero are injective. Let `h a a' b` in
`F₁ a a' ⊗ G₀ b` and `v a b b'` in `F₀ a ⊗ G₁ b b'` satisfy the cocycle relation
`fr (v a') - fl (v a) = gr (h b') - gl (h b)`. Then there is `e a b` in `F₀ a ⊗ G₀ b` with
`h = fr (e a') - fl (e a)` and `v = gr (e b') - gl (e b)`. -/
theorem exists_eq_rTensor_sub_and_eq_lTensor_sub
    (fl : ∀ a a', F₀ a →ₗ[k] F₁ a a') (fr : ∀ a a', F₀ a' →ₗ[k] F₁ a a')
    (hF : ∀ f : ∀ a, F₀ a, (∀ a a', fr a a' (f a') = fl a a' (f a)) → f = 0)
    (gl : ∀ b b', G₀ b →ₗ[k] G₁ b b') (gr : ∀ b b', G₀ b' →ₗ[k] G₁ b b')
    (hG : ∀ g : ∀ b, G₀ b, (∀ b b', gr b b' (g b') = gl b b' (g b)) → g = 0)
    (h : ∀ a a' b, F₁ a a' ⊗[k] G₀ b) (v : ∀ a b b', F₀ a ⊗[k] G₁ b b')
    (hv : ∀ a a' b b', (fr a a').rTensor _ (v a' b b') - (fl a a').rTensor _ (v a b b') =
      (gr b b').lTensor _ (h a a' b') - (gl b b').lTensor _ (h a a' b)) :
    ∃ e : ∀ a b, F₀ a ⊗[k] G₀ b,
      (∀ a a' b, h a a' b = (fr a a').rTensor _ (e a' b) - (fl a a').rTensor _ (e a b)) ∧
      (∀ a b b', v a b b' = (gr b b').lTensor _ (e a b') - (gl b b').lTensor _ (e a b)) := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  -- the complexes `C_Y⁰ → C_Y¹` and `C_X⁰ → C_X¹`
  let CY₀ : Type u := ∀ b, G₀ b
  let CY₁ : Type u := ∀ p : β × β, G₁ p.1 p.2
  let dY : CY₀ →ₗ[k] CY₁ := LinearMap.pi fun p ↦
    gr p.1 p.2 ∘ₗ LinearMap.proj p.2 - gl p.1 p.2 ∘ₗ LinearMap.proj p.1
  have hdY : LinearMap.ker dY = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun g hg ↦ hG g fun b b' ↦ ?_
    have := congr_fun hg (b, b')
    simp only [dY, CY₁, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      Pi.zero_apply, sub_eq_zero] at this
    exact this
  obtain ⟨ρ, hρ⟩ := dY.exists_leftInverse_of_injective hdY
  let CX₀ : Type u := ∀ a, F₀ a
  let CX₁ : Type u := ∀ p : α × α, F₁ p.1 p.2
  let dX : CX₀ →ₗ[k] CX₁ := LinearMap.pi fun p ↦
    fr p.1 p.2 ∘ₗ LinearMap.proj p.2 - fl p.1 p.2 ∘ₗ LinearMap.proj p.1
  have hdX : Function.Injective dX := by
    refine (injective_iff_map_eq_zero dX).mpr fun f hf ↦ hF f fun a a' ↦ ?_
    have := congr_fun hf (a, a')
    simp only [dX, CX₁, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      Pi.zero_apply, sub_eq_zero] at this
    exact this
  -- components of tensors with `CY₀` and `CY₁`
  let πY₀ (M : Type u) [AddCommGroup M] [Module k M] : M ⊗[k] CY₀ ≃ₗ[k] ∀ b, M ⊗[k] G₀ b :=
    piRight k k M G₀
  let πY₁ (M : Type u) [AddCommGroup M] [Module k M] :
      M ⊗[k] CY₁ ≃ₗ[k] ∀ p : β × β, M ⊗[k] G₁ p.1 p.2 :=
    piRight k k M fun p : β × β ↦ G₁ p.1 p.2
  have hπY₁dY (M : Type u) [AddCommGroup M] [Module k M] (t : M ⊗[k] CY₀) (p : β × β) :
      πY₁ M (dY.lTensor M t) p =
        (gr p.1 p.2).lTensor M (πY₀ M t p.2) - (gl p.1 p.2).lTensor M (πY₀ M t p.1) := by
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]; abel
    | tmul m g => simp [πY₁, πY₀, dY, tmul_sub, CY₁, CY₀, piRight_apply, piRightHom_tmul]
  have hπY₀r {M M' : Type u} [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
      (φ : M →ₗ[k] M') (t : M ⊗[k] CY₀) (b : β) :
      πY₀ M' (φ.rTensor CY₀ t) b = φ.rTensor _ (πY₀ M t b) := by
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
    | tmul m g => simp [πY₀, CY₀, piRight_apply, piRightHom_tmul]
  have hπY₁r {M M' : Type u} [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
      (φ : M →ₗ[k] M') (t : M ⊗[k] CY₁) (p : β × β) :
      πY₁ M' (φ.rTensor CY₁ t) p = φ.rTensor _ (πY₁ M t p) := by
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
    | tmul m g => simp [πY₁, CY₁, piRight_apply, piRightHom_tmul]
  -- the vertical and horizontal parts as tensors with `CY₁` and `CY₀`
  let V (a : α) : F₀ a ⊗[k] CY₁ := (πY₁ _).symm fun p ↦ v a p.1 p.2
  let H (a a' : α) : F₁ a a' ⊗[k] CY₀ := (πY₀ _).symm fun b ↦ h a a' b
  let E (a : α) : F₀ a ⊗[k] CY₀ := ρ.lTensor _ (V a)
  have hVH (a a' : α) : (fr a a').rTensor _ (V a') - (fl a a').rTensor _ (V a) =
      dY.lTensor _ (H a a') := by
    apply (πY₁ _).injective
    funext p
    rw [map_sub, Pi.sub_apply, hπY₁r, hπY₁r, hπY₁dY]
    simp only [V, H, LinearEquiv.apply_symm_apply]
    exact hv a a' p.1 p.2
  -- the vertical part is in the image of `1 ⊗ dY`
  let π : CY₁ →ₗ[k] CY₁ := LinearMap.id - dY ∘ₗ ρ
  have hπdY : π ∘ₗ dY = 0 := by
    simp only [π, LinearMap.sub_comp, LinearMap.id_comp, LinearMap.comp_assoc, hρ,
      LinearMap.comp_id, sub_self]
  have hpiLeft (t : CX₀ ⊗[k] CY₁) (p : α × α) :
      piLeft k CY₁ (fun p : α × α ↦ F₁ p.1 p.2) (dX.rTensor CY₁ t) p =
        (fr p.1 p.2).rTensor _ (piLeft k CY₁ F₀ t p.2) -
          (fl p.1 p.2).rTensor _ (piLeft k CY₁ F₀ t p.1) := by
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]; abel
    | tmul f c => simp [dX, CX₁, CX₀, sub_tmul, LinearMap.pi_apply]
  have hW : ∀ a, π.lTensor _ (V a) = 0 := by
    let Wt : CX₀ ⊗[k] CY₁ := (piLeft k CY₁ F₀).symm fun a ↦ π.lTensor _ (V a)
    have hWt : dX.rTensor CY₁ Wt = 0 := by
      apply (piLeft k CY₁ fun p : α × α ↦ F₁ p.1 p.2).injective
      funext p
      rw [hpiLeft, map_zero]
      simp only [Wt, LinearEquiv.apply_symm_apply]
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
        ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, LinearMap.comp_apply, ← map_sub,
        hVH, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hπdY, LinearMap.lTensor_zero,
        LinearMap.zero_apply]
      rfl
    have hinj : Function.Injective (dX.rTensor CY₁) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hdX
    have h0 : Wt = 0 := hinj (by rw [hWt, map_zero])
    intro a
    have := congr_fun (congrArg (piLeft k CY₁ F₀) h0) a
    simpa [Wt] using this
  have hE (a : α) : dY.lTensor _ (E a) = V a := by
    have h1 : V a = (dY ∘ₗ ρ).lTensor _ (V a) + π.lTensor _ (V a) := by
      rw [← LinearMap.add_apply, ← LinearMap.lTensor_add]
      simp [π]
    rw [h1, hW, add_zero, LinearMap.lTensor_comp_apply]
  -- the horizontal part is the coboundary of `E` in the first factor
  have hEH (a a' : α) : (fr a a').rTensor _ (E a') - (fl a a').rTensor _ (E a) = H a a' := by
    have hinj : Function.Injective (dY.lTensor (F₁ a a')) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (LinearMap.ker_eq_bot.mp hdY)
    apply hinj
    rw [← hVH, ← hE, ← hE, map_sub]
    simp only [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  refine ⟨fun a b ↦ πY₀ _ (E a) b, fun a a' b ↦ ?_, fun a b b' ↦ ?_⟩
  · have := congr_fun (congrArg (πY₀ _) (hEH a a')) b
    rw [map_sub, Pi.sub_apply, hπY₀r, hπY₀r] at this
    refine Eq.trans ?_ this.symm
    simp only [H, LinearEquiv.apply_symm_apply]
  · have := congr_fun (congrArg (πY₁ _) (hE a)) (b, b')
    rw [hπY₁dY] at this
    refine Eq.trans ?_ this.symm
    simp only [V, LinearEquiv.apply_symm_apply]


end TensorProduct
