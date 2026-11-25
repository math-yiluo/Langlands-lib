/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.BalancedActionAffineSections
import WeilConjectures.AlgebraicGeometry.AffineBasisRingActionGluing

/-! # Extending a balanced action to the direct-image algebra

Source: Stacks Project, Tags 01LX, 01SB and the relative-spectrum paragraph of 0897.
(blueprint: lem-weil-pbc-balanced-action-direct-image-module).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry


private theorem affine_section_ext {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (x y : M.val.obj (op U))
    (h : ∀ (V : X.affineOpens) (i : V.val ⟶ U),
      M.val.map i.op x = M.val.map i.op y) : x = y := by
  apply TopCat.Presheaf.IsSheaf.section_ext M.isSheaf
  intro z hz
  obtain ⟨V, hV, hzV, hVU⟩ := exists_isAffineOpen_mem_and_subset hz
  exact ⟨V, hVU, hzV, h ⟨V, hV⟩ (homOfLE hVU)⟩

/-- Extend the balanced action to the direct-image structure algebra, without realizing
its module on the base-changed scheme.

Source: Stacks Project, Tags 01LX and 01SB; Tag 0897, relative-spectrum paragraph.
(blueprint: lem-weil-pbc-balanced-action-direct-image-module).

Proof: Use balancedAction_affine_sections to obtain the unique balanced tensor
actions on all affine opens and their restriction compatibility. Extend them to
all opens by affineBasis_ringAction_gluing. Sheaf separatedness, using the affine
basis, extends the scalar and B-generator identities from affine opens to every
open. For the scalar identity use naturality of pi-sharp and semilinearity of
M's original restrictions. For the B identity use composition of structure-sheaf
restrictions and naturality of rho(b). Each extended ring map to additive
endomorphisms gives a module structure on the existing abelian sections of M.
The naturality equation is exactly semilinearity for those module structures.
PresheafOfModules.ofPresheaf therefore constructs the new module presheaf; its
underlying abelian presheaf is M's, so its sheaf condition is the original one.
The scalar identity makes the identity maps on sections linear in both
directions after restriction of scalars. They form the isomorphism e, whose
inverse identities are pointwise reflexivity. The B identity is the requested
equation since e is identity on sections. All data is constructed explicitly
from the unique action, rather than chosen from a bare module-existence claim.
Empty opens and the zero module are included by the same sheaf argument. -/
theorem balancedAction_directImage_module
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (M : X.Modules) (hM : M.IsQuasicoherent)
    (rho : B →+* End M)
    (hscalar : ∀ a : A, rho (algebraMap A B a) =
      .of (M.smulHom (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a))) :
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let Y := pullback f g
    let pi : Y ⟶ X := pullback.fst f g
    let fB : Y ⟶ Spec (.of B) := pullback.snd f g
    let C := (TopCat.Sheaf.pushforward CommRingCat.{u} pi.base).obj Y.sheaf
    let R := (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj C
    let S := SheafOfModules.restrictScalars.{u}
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map
        (show X.sheaf ⟶ C from ⟨pi.c⟩))
    ∃ (G : SheafOfModules.{u} R) (e : M ≅ S.obj G),
      ∀ (b : B) (U : X.Opens) (x : M.val.obj (op U)),
        (e.hom.val.app (op U)).hom ((rho b).asHom.val.app (op U) x) =
          Y.presheaf.map (homOfLE (le_top (a := pi ⁻¹ᵁ U))).op
            (((Scheme.ΓSpecIso (.of B)).inv ≫ fB.appTop).hom b) •
              (show G.val.obj (op U) from (e.hom.val.app (op U)).hom x) := by
  classical
  dsimp only
  let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let Y := pullback f g
  let pi : Y ⟶ X := pullback.fst f g
  let fB : Y ⟶ Spec (.of B) := pullback.snd f g
  let C := (TopCat.Sheaf.pushforward CommRingCat.{u} pi.base).obj Y.sheaf
  let R := (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj C
  let k : X.ringCatSheaf ⟶ R :=
    (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map
      (show X.sheaf ⟶ C from ⟨pi.c⟩)
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.val.presheaf, M.isSheaf⟩
  obtain ⟨tau, ⟨htau, hOX, hB⟩, _⟩ :=
    balancedAction_affine_sections f M hM rho hscalar
  obtain ⟨sigma, ⟨hnat, haff⟩, _⟩ := affineBasis_ringAction_gluing X R F tau htau
  have hscalar' (U : X.Opens) (r : X.presheaf.obj (op U))
      (x : M.val.obj (op U)) : sigma U (pi.app U r) x = r • x := by
    apply affine_section_ext M U
    intro V i
    change F.obj.map i.op (sigma U _ x) = _
    rw [hnat, haff]
    change tau V (C.obj.map i.op (pi.app U r)) (M.val.map i.op x) = _
    have hk := CategoryTheory.congr_fun (k.hom.naturality i.op) r
    change pi.app V.val (X.presheaf.map i.op r) =
      C.obj.map i.op (pi.app U r) at hk
    rw [← hk, hOX]
    exact (M.val.map_smul i.op r x).symm
  have hB' (U : X.Opens) (b : B) (x : M.val.obj (op U)) :
      sigma U (Y.presheaf.map (homOfLE (le_top (a := pi ⁻¹ᵁ U))).op
        (((Scheme.ΓSpecIso (.of B)).inv ≫ fB.appTop).hom b)) x =
        (rho b).asHom.val.app (op U) x := by
    apply affine_section_ext M U
    intro V i
    change F.obj.map i.op (sigma U _ x) = _
    rw [hnat, haff]
    have hres (a : Y.presheaf.obj (op (⊤ : Y.Opens))) :
        C.obj.map i.op (Y.presheaf.map
          (homOfLE (le_top (a := pi ⁻¹ᵁ U))).op a) =
        Y.presheaf.map (homOfLE (le_top (a := pi ⁻¹ᵁ V.val))).op a := by
      change Y.presheaf.map ((TopologicalSpace.Opens.map pi.base).map i).op
        (Y.presheaf.map _ a) = _
      rw [← CommRingCat.comp_apply, ← Y.presheaf.map_comp]
      rfl
    change tau V (C.obj.map i.op (Y.presheaf.map
      (homOfLE (le_top (a := pi ⁻¹ᵁ U))).op
        (((Scheme.ΓSpecIso (.of B)).inv ≫ fB.appTop).hom b)))
      (M.val.map i.op x) = M.val.map i.op ((rho b).asHom.val.app (op U) x)
    rw [hres, hB]
    exact PresheafOfModules.naturality_apply (rho b).asHom.val i.op x
  let inst : ∀ U : X.Opensᵒᵖ, Module (R.obj.obj U) (F.obj.obj U) :=
    fun U => Module.compHom _ (sigma U.unop)
  let P : PresheafOfModules.{u} R.obj :=
    PresheafOfModules.ofPresheaf F.obj (fun {U V} i r x => hnat V.unop U.unop i.unop r x)
  let G : SheafOfModules.{u} R := ⟨P, M.isSheaf⟩
  let e : M ≅ (SheafOfModules.restrictScalars k).obj G :=
    { hom := ⟨{
        app := fun U => ModuleCat.ofHom
          (X := M.val.obj U)
          (Y := ((SheafOfModules.restrictScalars k).obj G).val.obj U) {
          toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun r x => (hscalar' U.unop r x).symm }
        naturality := fun i => by ext x; rfl }⟩
      inv := ⟨{
        app := fun U => ModuleCat.ofHom
          (X := ((SheafOfModules.restrictScalars k).obj G).val.obj U)
          (Y := M.val.obj U) {
          toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun r x => hscalar' U.unop r x }
        naturality := fun i => by ext x; rfl }⟩
      hom_inv_id := by ext U x; rfl
      inv_hom_id := by ext U x; rfl }
  refine ⟨G, e, ?_⟩
  intro b U x
  exact (hB' U b x).symm

end AlgebraicGeometry
