/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase

import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.AlgebraicGeometry.ModuleSupportProperOverBase

/-! # Finite affine realizations of coherent algebras with proper support

Source: Stacks Project, Lemma 09ZT, last sentence, and Lemma 0CYS
(blueprint: lem-weil-pbc-coherent-algebra-affine-finite-proper).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option autoImplicit false

set_option hygiene false in
local notation "𝒪⁎" g:max => Under.mk (⟨(g).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (g).base).obj (Scheme.sheaf _))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- An affine realization of a coherent algebra is finite, and proper over the base
when its underlying module has proper support.
Source: Stacks Project, Lemma 09ZT, final sentence, and Lemma 0CYS (3).

Proof: On an affine U = Spec R, coherence implies that B(U) is a finite R-module.
The algebra isomorphism identifies g inverse U with Spec B(U), so g is finite.
Proper support gives a closed subscheme Z of X proper over S whose ideal annihilates B.
On every affine U with ideal J defining Z, the projection Y times_X Z to Y is Spec of
B(U) to B(U)/J B(U), an isomorphism because J B(U) = 0. These local identifications
show the projection is an isomorphism. Y times_X Z is finite over Z, hence proper over S,
and transporting properness along the projection gives properness of g composed with f.
The empty realization and zero algebra satisfy the same finite and quotient tests.
(blueprint: lem-weil-pbc-coherent-algebra-affine-finite-proper). -/
theorem coherent_algebra_affine_finite_proper
    {X Y S : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ S) [LocallyOfFiniteType f] (g : Y ⟶ X) [IsAffineHom g]
    (B : X.CommAlgebraSheaf) (α : B ≅ 𝒪⁎g)
    (hB : RingedSpace.IsCoherent X.toRingedSpace B.toModule)
    (hp : Scheme.Modules.HasSupportProperOver f B.toModule) :
    IsFinite g ∧ IsProper (g ≫ f) := by
  obtain ⟨hq, ht⟩ :=
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X B.toModule).mp hB
  have : B.toModule.IsQuasicoherent := hq
  have : B.toModule.IsFiniteType := ht
  have hg : IsFinite g := by
    refine (isFinite_iff g).mpr ⟨inferInstance, ?_⟩
    intro U hU
    have hf : Module.Finite Γ(X, U) Γ(B.toModule, U) :=
      Scheme.Modules.coherent_affine_sections_finite X B.toModule hB U hU
    let e : B.right.obj.obj (op U) ⟶ Γ(Y, g ⁻¹ᵁ U) := α.hom.right.hom.app (op U)
    let ei := α.inv.right.hom.app (op U)
    let φ : Γ(B.toModule, U) →ₗ[Γ(X, U)]
        (ModuleCat.restrictScalars (g.app U).hom).obj
          (ModuleCat.of Γ(Y, g ⁻¹ᵁ U) Γ(Y, g ⁻¹ᵁ U)) :=
      { toFun := e
        map_add' := e.hom.map_add
        map_smul' := fun a b ↦ by
          change B.right.obj.obj (op U) at b
          change e.hom (B.hom.hom.app (op U) a * b) = (g.app U).hom a * e.hom b
          rw [map_mul]
          congr 1
          exact ConcreteCategory.congr_hom
            (congrArg (fun k ↦ k.hom.app (op U)) α.hom.w) a }
    have : Module.Finite Γ(X, U)
        ((ModuleCat.restrictScalars (g.app U).hom).obj
          (ModuleCat.of Γ(Y, g ⁻¹ᵁ U) Γ(Y, g ⁻¹ᵁ U))) :=
      Module.Finite.of_surjective φ (by
        intro y
        refine ⟨ei y, ?_⟩
        have h := congrArg (fun k ↦ k.right.hom.app (op U)) α.inv_hom_id
        exact ConcreteCategory.congr_hom h y)
    exact this
  refine ⟨hg, ?_⟩
  have : IsFinite g := hg
  obtain ⟨Z, i, hi, hip, hkill, _⟩ :=
    (Scheme.Modules.module_support_proper_over_base f B.toModule).2.1.mp hp
  have : IsClosedImmersion i := hi
  have : IsProper (i ≫ f) := hip
  have hker : i.ker ≤ g.ker := by
    apply Scheme.IdealSheafData.le_ofIdeals_iff.mpr
    intro U a ha
    have ha' : a ∈ i.ker.idealOfOpens U.1 := by simpa using ha
    have hz := hkill U.1 a ha' (1 : B.right.obj.obj (op U.1))
    change B.hom.hom.app (op U.1) a * 1 = 0 at hz
    rw [mul_one] at hz
    change g.app U.1 a = 0
    have hw := ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.hom.app (op U.1)) α.hom.w) a
    change α.hom.right.hom.app (op U.1) (B.hom.hom.app (op U.1) a) =
      g.app U.1 a at hw
    rw [← hw, hz]
    exact map_zero _
  let l := IsClosedImmersion.lift i g hker
  have hl : l ≫ i = g := IsClosedImmersion.lift_fac i g hker
  have : IsFinite (l ≫ i) := hl.symm ▸ hg
  have : IsFinite l := IsFinite.of_comp l i
  have : IsProper (l ≫ (i ≫ f)) := inferInstance
  simpa only [← Category.assoc, hl] using this


end AlgebraicGeometry
