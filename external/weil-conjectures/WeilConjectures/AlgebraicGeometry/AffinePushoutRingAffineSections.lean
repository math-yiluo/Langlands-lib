/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.AffinePushoutRingSectionMapInjective
import WeilConjectures.AlgebraicGeometry.AffinePushoutRingSectionProducts
import WeilConjectures.AlgebraicGeometry.AffinePushoutRingSectionMapTmul
/-!
# Affine sections of the ring-sheaf pushout

Source: Stacks Project, Morphisms, Tag 01SB, affine reduction in the proof.
(blueprint: stage3-affine-pushout-ring-affine-sections).
-/

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
/-- The ring-sheaf pushout becomes a pushout of section rings on affine inverse images.
Source: Stacks Project, Morphisms, Tag 01SB.
(blueprint: stage3-affine-pushout-ring-affine-sections).
The affine inverse image W is affine since f is affine. Write D = Γ(X,V) and
C = Γ(U,W). The ring map D → C is f.app V.
Restrict f and the pushout diagram to this inverse image. The sheaf pushout is
the sheafification of the ring tensor presheaf. Identify its underlying module
with the pullback of the restricted-scalar regular module of f_*O_U: apply
the pushout scalar-extension cancellation comparison to the regular algebra
module. Inverse image of the regular module is the regular inverse-image
algebra module, and extending that module along t is the regular B-module
(the maps are x tensor a ↦ x*t(a) and x ↦ x tensor 1). This module is
quasi-coherent by affine pushforward. The affine module section comparison then
identifies its sections with C tensor_D C. The inverse-image adjunction unit
gives the second factor and b gives the first; their products define the
comparison. The affine comparison is an isomorphism. With the multiplication inherited from
the ring tensor presheaf, it is a ring isomorphism C tensor_D C → B(W). On
c tensor 1 it is b(c), and on 1 tensor d it is δ(d), where δ is the composite
of the inverse-image unit and t. Thus it carries the two canonical tensor
inclusions to the displayed maps. The tensor-product square is a pushout of
commutative rings; transport this property along the ring isomorphism. This
construction and argument also apply to the zero ring and the empty open. -/
theorem affine_pushout_ring_affine_sections [IsAffineHom f]
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B) (t : IA ⟶ B)
    (hpushout : IsPushout r₀ t₀ b t) (V : X.Opens) (hV : IsAffineOpen V) :
    let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f.base) CommRingCat.{u} (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology U)
    let δ : Γ(U, f ⁻¹ᵁ V) →+* B.obj.obj (op (f ⁻¹ᵁ V)) :=
      (t.hom.app (op (f ⁻¹ᵁ V))).hom.comp ((adj.unit.app A).hom.app (op V)).hom
    IsPushout (f.app V) (f.app V) (b.hom.app (op (f ⁻¹ᵁ V)))
      (CommRingCat.ofHom δ) := by
  classical
  dsimp only
  let : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  let q := affinePushoutSectionMap f B b t hpushout V
  have hsurj : Function.Surjective q.hom := by
    intro z
    obtain ⟨l, hl⟩ := affinePushoutSection_products f B b t hpushout V hV z
    refine ⟨(l.map fun x ↦ x.1 ⊗ₜ[Γ(X, V)] x.2).sum, ?_⟩
    rw [map_list_sum]
    simp only [q, List.map_map, Function.comp_def]
    simp_rw [affinePushoutSectionMap_tmul f B b t hpushout V]
    exact hl.symm
  have hinj : Function.Injective q.hom :=
    affinePushoutSectionMap_injective f B b t hpushout V hV
  let e := (RingEquiv.ofBijective q.hom ⟨hinj, hsurj⟩).toCommRingCatIso
  let ht := CommRingCat.isPushout_tensorProduct
    Γ(X, V) Γ(U, f ⁻¹ᵁ V) Γ(U, f ⁻¹ᵁ V)
  apply ht.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
  · rfl
  · rfl
  · exact ht.inl_desc _ _ (affinePushoutSection_comm f B b t hpushout V)
  · exact ht.inr_desc _ _ (affinePushoutSection_comm f B b t hpushout V)
end
end AlgebraicGeometry.Scheme.Modules
