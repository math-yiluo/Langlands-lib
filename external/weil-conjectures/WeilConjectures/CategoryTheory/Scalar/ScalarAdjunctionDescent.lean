/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.Whiskering

/-! # Descent of invertible adjoint transitions

Source: Zheng, Construction 4.1 and the adjunction argument in Lemma 4.10.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe a av b bv c cv d dv
open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory

/-- In a scalar-change square, an invertible adjoint transition descends along a
conservative inverse image, provided the two counits at its endpoints are invertible.
The direct-image comparison is required to be the mate of the inverse-image comparison.
Source: Zheng, Lemma 4.10. Proof: transpose the transition square first by scalar
change and then by geometric inverse image. The mate equation identifies the result
with the original adjoint transition composed with the two counits and the scalar
comparison. Every other arrow is invertible. Conservativity then applies to the
adjoint transition downstairs, including when its scalar-extension source is unbounded.
(blueprint: lem-pur-scalar-adjunction-descent). -/
theorem isIso_scalar_transpose_of_mate
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
    {CY : A ⥤ B} {RY : B ⥤ A} (ay : CY ⊣ RY)
    {CX : C ⥤ D} {RX : D ⥤ C} (ax : CX ⊣ RX)
    {Fm : A ⥤ C} {Gm : C ⥤ A} (am : Fm ⊣ Gm)
    {Fn : B ⥤ D} {Gn : D ⥤ B} (an : Fn ⊣ Gn)
    [Fn.ReflectsIsomorphisms]
    (γ : CY ⋙ Fn ≅ Fm ⋙ CX) (δ : RX ⋙ Gm ≅ Gn ⋙ RY)
    (hδ : ∀ (P : A) (Q : D) (f : Fn.obj (CY.obj P) ⟶ Q),
      ay.homEquiv P (Gn.obj Q) (an.homEquiv _ Q f) =
        am.homEquiv P (RX.obj Q)
          (ax.homEquiv (Fm.obj P) Q (γ.inv.app P ≫ f)) ≫ δ.hom.app Q)
    {Nm : A} {Nn : B} {Mm : C} {Mn : D}
    (em : Nm ≅ Gm.obj Mm) (en : Nn ≅ Gn.obj Mn)
    (τN : Nm ⟶ RY.obj Nn) (τM : Mm ⟶ RX.obj Mn)
    (hτ : τN ≫ RY.map en.hom = em.hom ≫ Gm.map τM ≫ δ.hom.app Mn)
    [IsIso (am.counit.app Mm)] [IsIso (an.counit.app Mn)]
    [IsIso ((ax.homEquiv Mm Mn).symm τM)] :
    IsIso ((ay.homEquiv Nm Nn).symm τN) := by
  let z := (ay.homEquiv Nm Nn).symm τN
  let f : Fn.obj (CY.obj Nm) ⟶ Mn :=
    (an.homEquiv (CY.obj Nm) Mn).symm (z ≫ en.hom)
  have hf : an.homEquiv _ Mn f = z ≫ en.hom := Equiv.apply_symm_apply _ _
  have hm := hδ Nm Mn f
  rw [hf, ay.homEquiv_naturality_right, Equiv.apply_symm_apply, hτ] at hm
  have hm' : am.homEquiv Nm (RX.obj Mn)
      (ax.homEquiv (Fm.obj Nm) Mn (γ.inv.app Nm ≫ f)) = em.hom ≫ Gm.map τM := by
    apply (cancel_mono (δ.hom.app Mn)).mp
    simpa only [Category.assoc] using hm.symm
  have ht : ax.homEquiv (Fm.obj Nm) Mn (γ.inv.app Nm ≫ f) =
      (am.homEquiv Nm (RX.obj Mn)).symm (em.hom ≫ Gm.map τM) := by
    exact (Equiv.eq_symm_apply _).mpr hm'
  have he : γ.inv.app Nm ≫ f =
      CX.map (Fm.map em.hom ≫ am.counit.app Mm) ≫
        (ax.homEquiv Mm Mn).symm τM := by
    apply (ax.homEquiv (Fm.obj Nm) Mn).injective
    rw [ht, ax.homEquiv_naturality_left]
    dsimp only [Functor.id_obj]
    rw [Equiv.apply_symm_apply]
    rw [am.homEquiv_naturality_right_symm, Adjunction.homEquiv_counit]
  have hi : IsIso (γ.inv.app Nm ≫ f) := by
    rw [he]
    infer_instance
  have hfi : IsIso f := IsIso.of_isIso_comp_left (γ.inv.app Nm) f
  have hfe : f = Fn.map z ≫ Fn.map en.hom ≫ an.counit.app Mn := by
    dsimp only [f]
    rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hzi : IsIso (Fn.map z) := by
    rw [hfe] at hfi
    have : IsIso (Fn.map z ≫ (Fn.map en.hom ≫ an.counit.app Mn)) := hfi
    exact IsIso.of_isIso_comp_right (Fn.map z) (Fn.map en.hom ≫ an.counit.app Mn)
  exact isIso_of_reflects_iso z Fn

end CategoryTheory
