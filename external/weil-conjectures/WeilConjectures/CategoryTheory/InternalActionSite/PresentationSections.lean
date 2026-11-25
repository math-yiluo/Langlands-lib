/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionSitePresentation

/-!
# Sections of the twisted module attached to an equivariant sheaf

Source: action-site construction (auxiliary; not a blueprint node).

For a presentation of equivariant sheaves as modules on the twisted site, we record the
sectionwise identification of the twisted module of an equivariant sheaf `M` at an object `X`
with the sections of `M` at `X`, its compatibility with twisted restrictions and with
morphisms, and a constructor of isomorphisms of twisted modules from sectionwise linear
equivalences compatible with all twisted restrictions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C] {K : Cᵒᵖ ⥤ GrpCat.{u}} [HasFiniteLimits C]
  {J : Precoverage C} {hJ : J.IsSiteForCoverings} {S : Sheaf J.toGrothendieck CommRingCat.{u}}

namespace Presentation

variable (P : Presentation K J hJ S)

/-- The sections at `X` of the twisted module of an equivariant sheaf are its sections at `X`. -/
noncomputable def sheafSections
    (M : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S)) (X : C) :
    (P.sheafEquivalence.functor.obj M).val.obj (op (Object.mk (K := K) X)) ≃ₗ[
      (baseRing J.toGrothendieck S).obj.obj (op X)] M.obj.val.obj (op X) :=
  let e : (P.sheafEquivalence.functor.obj M).val.obj (op (Object.mk (K := K) X)) ≃ₗ[
      (baseRing J.toGrothendieck S).obj.obj (op X)]
      (P.presheafEquivalence.functor.obj M.obj).obj (op (Object.mk (K := K) X)) :=
    ((PresheafOfModules.evaluation _ (op (Object.mk (K := K) X))).mapIso
      (P.underlying.app M)).symm.toLinearEquiv
  e.trans (P.sections M.obj X)

theorem sheafSections_restriction
    (M : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S))
    {X Y : C} (f : X ⟶ Y) (a : K.obj (op X))
    (m : (P.sheafEquivalence.functor.obj M).val.obj (op (Object.mk (K := K) Y))) :
    P.sheafSections M X ((P.sheafEquivalence.functor.obj M).val.map (opArrow K f a) m) =
      M.obj.action.act (op X) a (M.obj.val.map f.op (P.sheafSections M Y m)) := by
  have h := PresheafOfModules.naturality_apply (P.underlying.inv.app M) (opArrow K f a) m
  dsimp only [sheafSections]
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  erw [h]
  exact P.restriction M.obj f a _

theorem sheafSections_naturality
    {M N : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S)}
    (φ : M ⟶ N) (X : C)
    (m : (P.sheafEquivalence.functor.obj M).val.obj (op (Object.mk (K := K) X))) :
    P.sheafSections N X ((P.sheafEquivalence.functor.map φ).val.app _ m) =
      φ.hom.val.app (op X) (P.sheafSections M X m) := by
  have h := congrArg (fun k ↦ (k.app (op (Object.mk (K := K) X))).hom m)
    (P.underlying.inv.naturality φ)
  dsimp only [sheafSections]
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  erw [h]
  exact P.morphisms φ.hom X _

end Presentation

/-- Morphisms of twisted modules are determined by their components at the objects
`Object.mk X`. -/
theorem twisted_hom_ext {N₁ N₂ : SheafOfModules.{u} (twistedRing K J hJ S)} {φ ψ : N₁ ⟶ N₂}
    (h : ∀ (X : C) (m : N₁.val.obj (op (Object.mk (K := K) X))),
      φ.val.app _ m = ψ.val.app _ m) : φ = ψ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  exact h U.unop.base m

/-- An isomorphism of twisted modules from sectionwise linear equivalences compatible with all
twisted restrictions. -/
noncomputable def twistedIsoMk {N₁ N₂ : SheafOfModules.{u} (twistedRing K J hJ S)}
    (e : ∀ X : C, N₁.val.obj (op (Object.mk (K := K) X)) ≃ₗ[
      (baseRing J.toGrothendieck S).obj.obj (op X)] N₂.val.obj (op (Object.mk (K := K) X)))
    (he : ∀ {X Y : C} (f : X ⟶ Y) (a : K.obj (op X))
      (m : N₁.val.obj (op (Object.mk (K := K) Y))),
      e X (N₁.val.map (opArrow K f a) m) = N₂.val.map (opArrow K f a) (e Y m)) :
    N₁ ≅ N₂ :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ (e U.unop.base).toModuleIso) (fun U V g ↦ by
      ext m
      exact he g.unop.base g.unop.label m))

@[simp]
theorem twistedIsoMk_hom_app {N₁ N₂ : SheafOfModules.{u} (twistedRing K J hJ S)}
    (e : ∀ X : C, N₁.val.obj (op (Object.mk (K := K) X)) ≃ₗ[
      (baseRing J.toGrothendieck S).obj.obj (op X)] N₂.val.obj (op (Object.mk (K := K) X)))
    (he : ∀ {X Y : C} (f : X ⟶ Y) (a : K.obj (op X))
      (m : N₁.val.obj (op (Object.mk (K := K) Y))),
      e X (N₁.val.map (opArrow K f a) m) = N₂.val.map (opArrow K f a) (e Y m))
    (X : C) (m : N₁.val.obj (op (Object.mk (K := K) X))) :
    (twistedIsoMk e he).hom.val.app _ m = e X m :=
  rfl

end CategoryTheory.InternalActionSite
