/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.PresheafChangeOfRingsAdjunction

/-!
# The tensor change-of-rings adjunction on sheaves of modules

Source: Stacks Project, Sheaves on Spaces, Lemma 6.20.2, Tag 008A
(blueprint: lem-pc-module-change-of-rings-adjunction).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace
open scoped ChangeOfRings

namespace SheafOfModules

variable (X : TopCat.{u}) (A B : X.Sheaf CommRingCat.{u}) (α : A ⟶ B)

set_option hygiene false in
local notation "𝓙" => Opens.grothendieckTopology X
set_option hygiene false in
local notation "𝓡" S => (sheafCompose 𝓙 (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓪" => (sheafCompose 𝓙 (forget₂ CommRingCat.{u} RingCat.{u})).map α
set_option hygiene false in
local notation "𝓣" M => changeOfRings.{u, u, u} (J := 𝓙) (R₁ := A) (R₂ := B) α M
set_option hygiene false in
local notation "η" M => CategoryTheory.toSheafify 𝓙
  (changeOfRingsPresheaf.{u, u, u} (J := 𝓙) (R₁ := A) (R₂ := B) α M).presheaf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Change of rings by the sheafified sectionwise tensor product is left adjoint to
restriction of scalars. The hom correspondence first applies the sheafification unit
to `1 ⊗ m`, then evaluates the map. Its naturality in both modules is part of `adj`.
Source: Stacks Project, Tag 008A (blueprint: lem-pc-module-change-of-rings-adjunction).

Proof: (1) Apply the sectionwise tensor adjunction and compatibility with restrictions
(`lem-pc-presheaf-change-of-rings-adjunction`, Tag 006R) to obtain the natural presheaf
hom bijection. The right-hand homs are sheaf homs since both modules are sheaves
(`situation-conventions`). (2) Apply the sheafification universal property
(`def-weil-presheaf-modules-sheafification`, Tag 0089) to the presheaf of tensors
(`def-pur-sheaf-tensor-product`). Since the target is a sheaf, precomposition with the
sheafification unit is a bijection. (3) Compose these natural bijections. They send `u`
to `m ↦ u(η(1 ⊗ m))`. Naturality defines the change-of-rings functor on morphisms and
supplies the adjunction; its objects are the already defined `changeOfRings α M`.
The equality `h` only transports between this functor's objects and those tensors. -/
theorem exists_changeOfRingsAdjunction :
    ∃ (E : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
      (h : ∀ M : SheafOfModules.{u} (𝓡 A), E.obj M = 𝓣 M)
      (adj : E ⊣ restrictScalars 𝓪),
      ∀ (M : SheafOfModules.{u} (𝓡 A)) (N : SheafOfModules.{u} (𝓡 B))
        (f : (𝓣 M) ⟶ N) (U : (Opens X)ᵒᵖ) (m : M.val.obj U),
        ((adj.homEquiv M N) (eqToHom (h M) ≫ f)).val.app U m =
          f.val.app U ((η M).app U
            ((1 : B.presheaf.obj U) ⊗ₜ[A.presheaf.obj U, (α.hom.app U).hom] m)) := by
  classical
  obtain ⟨T, q, e, hres, _, he, _, _, _⟩ :=
    PresheafOfModules.changeOfRingsAdjunction.{u, u, u} X A B α
  let hp (M : SheafOfModules.{u} (𝓡 A)) :
      changeOfRingsPresheaf.{u, u, u} (J := 𝓙) α M ≅ T.obj M.val := by
    refine PresheafOfModules.isoMk (q M.val) ?_
    intro U V i
    let : Module (A.presheaf.obj V)
        ((ModuleCat.restrictScalars ((𝓡 A).obj.map i).hom).obj (M.val.obj V)) :=
      inferInstanceAs (Module (A.presheaf.obj V) (M.val.obj V))
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change (q M.val V).hom (changeOfRingsMap.{u, u, u} (J := 𝓙) α M i _) = _
    rw [show changeOfRingsMap.{u, u, u} (J := 𝓙) α M i
        ((1 : B.presheaf.obj U) ⊗ₜ[A.presheaf.obj U, (α.hom.app U).hom] m) =
        (B.presheaf.map i 1) ⊗ₜ[A.presheaf.obj V, (α.hom.app V).hom]
          (M.val.map i m) from
      Classical.choose_spec (exists_changeOfRingsMap.{u, u, u} (J := 𝓙) α M i) 1 m]
    exact (hres M.val U V i 1 m).symm
  let es (M : SheafOfModules.{u} (𝓡 A)) (N : SheafOfModules.{u} (𝓡 B)) :
      ((𝓣 M) ⟶ N) ≃ (M ⟶ (restrictScalars 𝓪).obj N) :=
    (PresheafOfModules.sheafificationHomEquiv (𝟙 (𝓡 B).obj)).trans
      (((Iso.homCongr (hp M) (Iso.refl N.val)).trans (e M.val N.val)).trans
        { toFun := fun g ↦ ⟨g⟩
          invFun := fun g ↦ g.val
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl })
  have hes (M : SheafOfModules.{u} (𝓡 A)) (N : SheafOfModules.{u} (𝓡 B))
      (f : (𝓣 M) ⟶ N) (U : (Opens X)ᵒᵖ) (m : M.val.obj U) :
      (es M N f).val.app U m =
        f.val.app U ((η M).app U
          ((1 : B.presheaf.obj U) ⊗ₜ[A.presheaf.obj U, (α.hom.app U).hom] m)) := by
    change (e M.val N.val
      ((hp M).inv ≫ PresheafOfModules.sheafificationHomEquiv (𝟙 (𝓡 B).obj) f)).app
        U m = _
    rw [he]
    change (PresheafOfModules.sheafificationHomEquiv (𝟙 (𝓡 B).obj) f).app U
      ((hp M).inv.app U ((q M.val U).hom _)) = _
    change (PresheafOfModules.sheafificationHomEquiv (𝟙 (𝓡 B).obj) f).app U
      ((q M.val U).inv ((q M.val U).hom _)) = _
    have hc (x : (ModuleCat.extendScalars (α.hom.app U).hom).obj (M.val.obj U)) :
        (q M.val U).inv ((q M.val U).hom x) = x :=
      ConcreteCategory.congr_hom (q M.val U).hom_inv_id x
    rw [hc]
    rfl
  have hn : ∀ M N N' (g : N ⟶ N') (f : (𝓣 M) ⟶ N),
      es M N' (f ≫ g) = es M N f ≫ (restrictScalars 𝓪).map g := by
    intro M N N' g f
    ext U m
    rw [hes]
    change g.val.app U (f.val.app U _) = g.val.app U ((es M N f).val.app U m)
    rw [hes]
  refine ⟨Adjunction.leftAdjointOfEquiv es hn, fun _ ↦ rfl,
    Adjunction.adjunctionOfEquivLeft es hn, ?_⟩
  intro M N f U m
  simp only [eqToHom_refl, Category.id_comp, Adjunction.adjunctionOfEquivLeft,
    Adjunction.mkOfHomEquiv_homEquiv]
  exact hes M N f U m

end SheafOfModules
