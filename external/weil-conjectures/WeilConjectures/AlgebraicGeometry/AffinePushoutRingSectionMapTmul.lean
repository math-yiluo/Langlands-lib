/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.AffinePushoutRingSectionMap
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {U X : Scheme.{u}} (f : U ⟶ X)
set_option hygiene false in
local notation "A" => (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
set_option hygiene false in
local notation "ρ" => (show X.sheaf ⟶ A from ⟨f.c⟩)
set_option hygiene false in
local notation "IA" => TopCat.Sheaf.inverseImageRing f.base A
set_option hygiene false in
local notation "r₀" => tensorPullbackRingMap f
set_option hygiene false in
local notation "t₀" =>
  (TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map ρ
/-- On pure tensors the constructed map multiplies the two section legs.
Source: Stacks Project, Tag 01SB (blueprint: stage3-affine-pushout-ring-section-map-tmul). -/
theorem affinePushoutSectionMap_tmul
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B) (t : IA ⟶ B)
    (hpushout : IsPushout r₀ t₀ b t) (V : X.Opens) :
    letI : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
    ∀ c d : Γ(U, f ⁻¹ᵁ V),
      (affinePushoutSectionMap f B b t hpushout V).hom (c ⊗ₜ[Γ(X, V)] d) =
        (b.hom.app (op (f ⁻¹ᵁ V))).hom c * affinePushoutSectionDelta f B t V d := by
  let : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  intro c d
  let ht := CommRingCat.isPushout_tensorProduct
    Γ(X, V) Γ(U, f ⁻¹ᵁ V) Γ(U, f ⁻¹ᵁ V)
  have hl := ht.inl_desc (b.hom.app (op (f ⁻¹ᵁ V)))
    (CommRingCat.ofHom (affinePushoutSectionDelta f B t V))
    (affinePushoutSection_comm f B b t hpushout V)
  have hr := ht.inr_desc (b.hom.app (op (f ⁻¹ᵁ V)))
    (CommRingCat.ofHom (affinePushoutSectionDelta f B t V))
    (affinePushoutSection_comm f B b t hpushout V)
  have hlc := congrArg (fun q ↦ q.hom c) hl
  have hrd := congrArg (fun q ↦ q.hom d) hr
  change (affinePushoutSectionMap f B b t hpushout V).hom
    (c ⊗ₜ[Γ(X, V)] 1) = _ at hlc
  change (affinePushoutSectionMap f B b t hpushout V).hom
    (1 ⊗ₜ[Γ(X, V)] d) = _ at hrd
  calc
    _ = (affinePushoutSectionMap f B b t hpushout V).hom
        ((c ⊗ₜ[Γ(X, V)] 1) * (1 ⊗ₜ[Γ(X, V)] d)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    _ = _ := by
      rw [map_mul, hlc, hrd]
      rfl

end
end AlgebraicGeometry.Scheme.Modules
