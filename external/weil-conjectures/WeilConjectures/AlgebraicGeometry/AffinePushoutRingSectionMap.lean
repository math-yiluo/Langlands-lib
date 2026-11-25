/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.AffinePushoutRingSectionComm
public import Mathlib.Algebra.Category.Ring.Constructions
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
/-- The tensor section map is constructed by the ring tensor universal property.
It is not chosen from a postponed existence theorem.
Source: Stacks Project, Tag 01SB (blueprint: stage3-affine-pushout-ring-section-map). -/
def affinePushoutSectionMap
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B) (t : IA ⟶ B)
    (hpushout : IsPushout r₀ t₀ b t) (V : X.Opens) :
    letI : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
    CommRingCat.of (Γ(U, f ⁻¹ᵁ V) ⊗[Γ(X, V)] Γ(U, f ⁻¹ᵁ V)) ⟶
      CommRingCat.of (B.obj.obj (op (f ⁻¹ᵁ V))) := by
  let : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  exact (CommRingCat.isPushout_tensorProduct
    Γ(X, V) Γ(U, f ⁻¹ᵁ V) Γ(U, f ⁻¹ᵁ V)).desc
      (b.hom.app (op (f ⁻¹ᵁ V)))
      (CommRingCat.ofHom (affinePushoutSectionDelta f B t V))
      (affinePushoutSection_comm f B b t hpushout V)

end
end AlgebraicGeometry.Scheme.Modules
