/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
public import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.CategoryTheory.ProperBaseChange.ContinuousCocontinuousRingedRestriction

/-! # Geometric restriction for the twisted action site

Source: the agent-formulated twisted variant of Stacks Tag 00W0, original steps 6.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.TwistedActionRingedSite

-- Changing the source ring along an isomorphism leaves both set functors fixed.
-- The module direct image first restricts scalars along that isomorphism.
private noncomputable def transportSource
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A A' : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism A B) (c : A ≅ A') : RingedToposMorphism A' B where
  inverse := f.inverse
  direct := f.direct
  adj := f.adj
  leftExact := f.leftExact
  ringMap := f.ringMap ≫ (sheafCompose J (forget RingCat)).map c.hom
  ring_zero := by
    intro T z hz U t
    change (c.hom.hom.app U).hom (((f.inverse.map z) ≫ f.ringMap).hom.app U t) = 0
    rw [f.ring_zero T z hz U t]
    exact (c.hom.hom.app U).hom.map_zero
  ring_one := by
    intro T z hz U t
    change (c.hom.hom.app U).hom (((f.inverse.map z) ≫ f.ringMap).hom.app U t) = 1
    rw [f.ring_one T z hz U t]
    exact (c.hom.hom.app U).hom.map_one
  ring_add := by
    intro T x y z hz U t
    change (c.hom.hom.app U).hom (((f.inverse.map z) ≫ f.ringMap).hom.app U t) =
      (c.hom.hom.app U).hom (((f.inverse.map x) ≫ f.ringMap).hom.app U t) +
        (c.hom.hom.app U).hom (((f.inverse.map y) ≫ f.ringMap).hom.app U t)
    rw [f.ring_add T x y z hz U t]
    exact (c.hom.hom.app U).hom.map_add _ _
  ring_mul := by
    intro T x y z hz U t
    change (c.hom.hom.app U).hom (((f.inverse.map z) ≫ f.ringMap).hom.app U t) =
      (c.hom.hom.app U).hom (((f.inverse.map x) ≫ f.ringMap).hom.app U t) *
        (c.hom.hom.app U).hom (((f.inverse.map y) ≫ f.ringMap).hom.app U t)
    rw [f.ring_mul T x y z hz U t]
    exact (c.hom.hom.app U).hom.map_mul _ _
  modules := SheafOfModules.pushforward (F := 𝟭 C) c.hom ⋙ f.modules
  additive := by
    let : (SheafOfModules.pushforward (F := 𝟭 C) c.hom).Additive :=
      ⟨by intro M N q r; ext U x; rfl⟩
    infer_instance
  underlying := Functor.isoWhiskerLeft (SheafOfModules.pushforward (F := 𝟭 C) c.hom)
    f.underlying
  module_linear := by
    intro M T a x y z hz U t
    exact f.module_linear _ T a x y z hz U t

private noncomputable def scalarEquivalence
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {A A' : Sheaf J RingCat.{u}} (c : A ≅ A') :
    SheafOfModules.{u} A' ≌ SheafOfModules.{u} A := by
  let : (Equivalence.refl (C := C)).functor.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let : (Equivalence.refl (C := C)).inverse.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  exact SheafOfModules.pushforwardPushforwardEquivalence (Equivalence.refl (C := C))
    c.hom c.inv (by
      ext U x
      change A'.obj.map (𝟙 _) x = c.hom.hom.app U (c.inv.hom.app U x)
      rw [Functor.map_id_apply]
      exact (congrArg (fun f ↦ f.hom.app U x) c.inv_hom_id).symm) (by
      ext U x
      change A.obj.map (𝟙 _) (c.inv.hom.app U (c.hom.hom.app U x)) = x
      rw [Functor.map_id_apply]
      exact congrArg (fun f ↦ f.hom.app U x) c.hom_inv_id)

-- Heterogeneous sectionwise identity is exactly transport along the given
-- equality of inverse-image functors.
private theorem map_eq_transport
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : Sheaf K (Type u) ⥤ Sheaf J (Type u)} (h : F = G)
    (M : Sheaf K (Type u)) (k : F.obj M ⟶ G.obj M)
    (hk : ∀ (U : Cᵒᵖ) (x : (F.obj M).obj.obj U), HEq (k.hom.app U x) x) :
    k = (eqToHom h).app M := by
  subst G
  ext U x
  exact eq_of_heq (hk U x)

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (s : C ≌ C) [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    (R : Sheaf J CommRingCat.{u})
    (a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R)

omit [s.functor.IsContinuous J J] in
/-- Geometric restriction and its ordinary module-restriction adjunction.

Source: original step 6 of the agent-formulated twisted variant of Stacks 00W0,
`sites.tex`, proposition-sheaves-on-group; Stacks 00XO and 04IE
(blueprint: lem-sf-twisted-action-geometric-restriction).

Proof: apply continuous_cocontinuous_ringed_restriction to the coefficient ring
on the fixed action site, using the supplied cocontinuity of inclusion. This gives
the set adjunction and the module adjunction for the literally restricted ring.
The heterogeneous sectionwise identity of its structural map identifies that map
with transport along its inverse-image equality: after equality induction every
component is the identity. Now transport the source coefficient ring through
coefficientRestriction. Postcompose the structural map with that ring isomorphism;
its ring-operation laws follow from those of the original map and the ring map.
Precompose the module direct image with restriction of scalars in the opposite
direction. This leaves its underlying set functor fixed, and its linearity formula
is the original one with the scalar action transported. Scalar restriction along
a ring isomorphism is an equivalence, obtained from Mathlib's module pushforward
equivalence on the identity site. Compose the original module adjunction with the
inverse scalar-equivalence adjunction to get ordinary module restriction as left
adjoint. The structural map is invertible and has exactly the displayed formula.
No fixed-pair equivalence, underlying Site construction, or nonempty site is used. -/
theorem geometricRestriction [HasPullbacks C] (S : Site J s R a) :
    letI := S.category
    letI := S.inclusion_continuous
    S.inclusion.IsCocontinuous J S.topology →
    ∃ (g : RingedToposMorphism (ring R) (ring S.coefficient))
      (h : g.inverse = S.inclusion.sheafPushforwardContinuous (Type u) J S.topology),
      IsIso g.ringMap ∧
      g.ringMap =
        (eqToHom h).app ((sheafCompose S.topology (forget RingCat)).obj
          (ring S.coefficient)) ≫
          (sheafCompose J (forget RingCat)).map
            ((sheafCompose J (forget₂ CommRingCat RingCat)).map
              S.coefficientRestriction.hom) ∧
      Nonempty (SheafOfModules.pushforward
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map
          S.coefficientRestriction.inv) ⊣ g.modules) := by
  let := S.category
  let := S.inclusion_continuous
  intro hc
  let : S.inclusion.IsCocontinuous J S.topology := hc
  let c := (sheafCompose J (forget₂ CommRingCat RingCat)).mapIso S.coefficientRestriction
  obtain ⟨f, hf, hr, ⟨adj₀⟩⟩ := continuous_cocontinuous_ringed_restriction
    J S.topology S.inclusion (ring S.coefficient)
  have hMap := map_eq_transport hf
    ((sheafCompose S.topology (forget RingCat)).obj (ring S.coefficient)) f.ringMap hr
  let g := transportSource f c
  let E := scalarEquivalence c
  have adj := adj₀.comp E.symm.toAdjunction
  refine ⟨g, hf, ?_, ?_, ⟨?_⟩⟩
  · change IsIso (f.ringMap ≫ (sheafCompose J (forget RingCat)).map c.hom)
    rw [hMap]
    infer_instance
  · change f.ringMap ≫ (sheafCompose J (forget RingCat)).map c.hom =
      (eqToHom hf).app _ ≫ (sheafCompose J (forget RingCat)).map c.hom
    rw [hMap]
  · exact adj

end CategoryTheory.TwistedActionRingedSite
