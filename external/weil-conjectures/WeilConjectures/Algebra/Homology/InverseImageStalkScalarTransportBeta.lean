/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Tensor transport along a semilinear additive equivalence

Source: Stacks Project, Sheaves, Tag 0098, balanced tensor construction.
(blueprint: lem-pc-ringed-inverse-image-stalk-scalar-transport-beta).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped ChangeOfRings

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Tensor transport through a ring equivalence and a compatible additive equivalence.
Source: Stacks Project, Sheaves, Tag 0098, proof of the stalk pullback formula.

Proof: map b tensor m to b tensor c(m). Additivity holds in both factors;
balancing follows from c(r m) = e(r)c(m) and the source scalar map psi composed
with e. For the inverse use b tensor n mapping to b tensor c inverse(n).
Apply the forward compatibility to e inverse(s) and c inverse(n) and cancel c
to prove inverse compatibility. The resulting balanced maps are B-linear because
B acts by multiplication on the first factor. The two composites fix every pure
tensor; tensor induction proves they are identities. Zero rings and modules
satisfy the same equations. No flatness is required.
(blueprint: lem-pc-ringed-inverse-image-stalk-scalar-transport-beta). -/
theorem exists_inverseImage_stalk_scalar_transport_beta
    {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
    (k : R →+* S) (hk : Function.Bijective k) (ψ : S →+* B)
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} S)
    (c : M ≃+ N) (hc : ∀ (r : R) (m : M), c (r • m) = k r • c m) :
    ∃ β : (ModuleCat.extendScalars (ψ.comp k)).obj M ≅
        (ModuleCat.extendScalars ψ).obj N,
      ∀ (b : B) (m : M), β.hom (b ⊗ₜ[_, ψ.comp k] m) =
        b ⊗ₜ[_, ψ] c m := by
  let e := RingEquiv.ofBijective k hk
  let := RingHomInvPair.of_ringEquiv e
  let := RingHomInvPair.of_ringEquiv_symm e
  let : Module R B := Module.compHom B (ψ.comp k)
  let : Module S B := Module.compHom B ψ
  let d : B ≃ₛₗ[(e : R →+* S)] B :=
    { __ := AddEquiv.refl B
      map_smul' := by intro r b; rfl }
  let c' : M ≃ₛₗ[(e : R →+* S)] N :=
    { __ := c
      map_smul' := hc }
  let q := TensorProduct.congr d c'
  let q' : (ModuleCat.extendScalars (ψ.comp k)).obj M ≃ₗ[B]
      (ModuleCat.extendScalars ψ).obj N :=
    { __ := q.toAddEquiv
      map_smul' := by
        intro b z
        induction z using TensorProduct.inductionOn with
        | tmul b' m =>
          change B at b'
          change q ((b * b') ⊗ₜ[R] m) = b • q (b' ⊗ₜ[R] m)
          rfl
        | add z w hz hw =>
          change q (b • (z + w)) = b • q (z + w)
          change q (b • z) = b • q z at hz
          change q (b • w) = b • q w at hw
          rw [smul_add, map_add, hz, hw, map_add, smul_add] }
  refine ⟨q'.toModuleIso, ?_⟩
  intro b m
  rfl

end
