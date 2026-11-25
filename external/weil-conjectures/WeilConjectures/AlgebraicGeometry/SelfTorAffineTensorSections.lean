/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SelfTorAffineSection
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.AlgebraicGeometry.SelfTorAffineChartSections
import WeilConjectures.AlgebraicGeometry.LocallyQuasicoherentAffinePullbackSections

/-! # Affine sections of the chart model after tensor pullback

Source: Stacks Project, Tags 01I9, lemma-widetilde-pullback, and 0096,
lemma-pullback-modules.
(blueprint: new-v2-self-tor-affine-tensor-sections). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- Tensor extension of an arbitrary affine module computes the chart model sections.
Source: Stacks Project, Tag 01I9(1), lemma-widetilde-pullback; Tag 01I7,
lemma-compare-constructions; Tag 0096, lemma-pullback-modules.
(blueprint: new-v2-self-tor-affine-tensor-sections).
Proof: Put V=i inverse-image U, A=Gamma(Y,U), B=Gamma(Z,V), and j:U to Y.
Because i is affine, V is affine. Restrict j_* of the associated M back to U.
The open-immersion restriction comparison identifies this restriction with
that associated module, since j inverse-image U is all of U. Its map on
sections is inverse to the restriction map used in selfTorAffineSection.
Restriction commutes with tensor pullback; identify the resulting sheaf on V
with the pullback of the associated module along V to U. Use the affine
pullback comparison on these two affine schemes (not on all of Y): it gives
B tensor_A M as the sections over V. The tilde adjunction unit is an
isomorphism, so its inverse identifies the original sections with M.
Naturality of the open restriction and tensor-pullback adjunction units shows
that the composite sends b tensor m to b times selfTorAffineSection(i,U,M,m).
This also proves B-linearity. Each comparison is an isomorphism, giving the
claimed equivalence. If V is empty then B and both modules are zero. This
argument is local on U, so it does not require the pushforward along j to be
quasi-coherent on all of Y, nor any quasi-separatedness assumption on Y. -/
theorem exists_selfTor_affine_tensor_sections
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsAffineHom i]
    (U : Y.affineOpens) (M : ModuleCat.{u} (Γ(Y, U.1) : Type u)) :
    letI : Algebra Γ(Y, U.1) Γ(Z, i ⁻¹ᵁ U.1) := (i.app U.1).hom.toAlgebra
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    ∃ e : (Γ(Z, i ⁻¹ᵁ U.1) ⊗[Γ(Y, U.1)] M) ≃ₗ[Γ(Z, i ⁻¹ᵁ U.1)]
        (T.obj M).val.obj (op (i ⁻¹ᵁ U.1)),
      ∀ (b : Γ(Z, i ⁻¹ᵁ U.1)) (m : M),
        e (b ⊗ₜ[Γ(Y, U.1)] m) = b • selfTorAffineSection i U M m := by
  classical
  dsimp only
  let : Algebra Γ(Y, U.1) Γ(Z, i ⁻¹ᵁ U.1) := (i.app U.1).hom.toAlgebra
  let L := (tilde.functor Γ(Y, U.1)).obj M
  let C := (Scheme.Modules.pushforward U.1.ι).obj
    ((Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj L)
  obtain ⟨e₀, hC, he₀⟩ := exists_selfTor_affine_chart_sections U M
  obtain ⟨e₁, he₁⟩ := exists_locallyQuasicoherent_affine_pullback_sections i U C hC
  let e := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl Γ(Z, i ⁻¹ᵁ U.1) Γ(Z, i ⁻¹ᵁ U.1)) e₀
  refine ⟨e.trans e₁, ?_⟩
  intro b m
  change e₁ (b ⊗ₜ[Γ(Y, U.1)] e₀ m) = _
  rw [he₁, he₀]
  rfl

end AlgebraicGeometry
