/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Extensionality on original balanced tensor sections

Source: Stacks Project, Cohomology, Tag 08DE, proof.
(blueprint: lem-pc-balanced-sheaf-tensor-original-sections-ext)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory MonoidalCategory TopologicalSpace
open scoped ChangeOfRings

namespace SheafOfModules

variable {Z : TopCat.{u}} {R B : Z.Sheaf CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡" E =>
  (sheafCompose (Opens.grothendieckTopology Z) (forget₂ CommRingCat.{u} RingCat.{u})).obj E
set_option hygiene false in
local notation "𝓻" a =>
  (sheafCompose (Opens.grothendieckTopology Z) (forget₂ CommRingCat.{u} RingCat.{u})).map a

-- Mixed scalar structures require additional definitional equality checks.
/-- Original extension sections generate the restricted sheaf tensor for testing maps.
Source: Stacks Project, Modules on Sites, Tag 0GMW; Cohomology, Tag 08DE, proof.

Proof: the module sheafification unit of the extension presheaf E is inverted by
sheafification. The source library's W_whiskerLeft shows that tensoring this unit
with M.val is still inverted. Sheafify this tensor map, compose with the inverse
of tensorObjIsoSheafification, and restrict scalars: the resulting map q is an
isomorphism onto the source of f and g. Precompose with q and forget to abelian
sheaves. The abelian-sheafification adjunction reduces equality to the original
presheaf sections. Induct on the outer B-tensor and then on the inner R-tensor.
The zero and addition cases follow from additivity. On m tensor (b tensor n),
naturality of the module sheafification unit identifies both evaluations with
exactly the tests in h. No B-linearity of f or g is needed. The localization and
tensor induction arguments include empty spaces and zero rings or modules.
(blueprint: lem-pc-balanced-sheaf-tensor-original-sections-ext) -/
theorem balancedTensor_originalSections_hom_ext (α : R ⟶ B)
    (M : SheafOfModules.{u} (𝓡 B)) (N : SheafOfModules.{u} (𝓡 R))
    {H : SheafOfModules.{u} (𝓡 R)}
    {f g : (restrictScalars (𝓻 α)).obj
        ((monoidalCategory B).tensorObj M (changeOfRings.{u, u, u} α N)) ⟶ H}
    (h : ∀ (W : (Opens Z)ᵒᵖ) (m : M.val.obj W)
      (b : B.obj.obj W) (n : N.val.obj W),
      f.val.app W
        ((tensorObjIsoSheafification M (changeOfRings.{u, u, u} α N)).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
          (M.val ⊗ (changeOfRings.{u, u, u} α N).val)).app W
            (m ⊗ₜ[B.obj.obj W]
              ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
                (changeOfRingsPresheaf.{u, u, u} α N)).app W
                  (b ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] n)))) =
      g.val.app W
        ((tensorObjIsoSheafification M (changeOfRings.{u, u, u} α N)).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
          (M.val ⊗ (changeOfRings.{u, u, u} α N).val)).app W
            (m ⊗ₜ[B.obj.obj W]
              ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
                (changeOfRingsPresheaf.{u, u, u} α N)).app W
                  (b ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] n))))) :
    f = g := by
  let := monoidalCategory B
  let J := Opens.grothendieckTopology Z
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)
  let S := PresheafOfModules.sheafification (𝟙 (𝓡 B).obj)
  let E := changeOfRingsPresheaf.{u, u, u} α N
  let η := adj.unit.app E
  have hη : J.W ((PresheafOfModules.toPresheaf (𝓡 B).obj).map η) := by
    change (J.W.inverseImage (PresheafOfModules.toPresheaf (𝓡 B).obj)) η
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (𝓡 B).obj)]
    change IsIso (S.map η)
    infer_instance
  have hl := W_whiskerLeft B M.val hη
  have hl' : IsIso (S.map (M.val ◁ η)) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (𝓡 B).obj)] at hl
    exact hl
  let i := asIso (S.map (M.val ◁ η)) ≪≫
    (tensorObjIsoSheafification M (S.obj E)).symm
  let q := ((restrictScalars (𝓻 α)).mapIso i).hom
  have : IsIso q := Iso.isIso_hom ((restrictScalars (𝓻 α)).mapIso i)
  apply (cancel_epi q).mp
  apply (toSheaf (𝓡 R)).map_injective
  let a := CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{u}
  apply (a.homEquiv (M.val ⊗ E).presheaf ((toSheaf (𝓡 R)).obj H)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext W t
  induction t using TensorProduct.inductionOn with
  | add t s ht hs => simp only [map_add, ht, hs]
  | tmul m z =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul b n =>
      have hn := adj.unit.naturality (M.val ◁ η)
      have he := congrArg (fun k ↦ (k.app W) (m ⊗ₜ[B.obj.obj W]
        (b ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] n))) hn
      change (adj.unit.app (M.val ⊗ (S.obj E).val)).app W
          (m ⊗ₜ[B.obj.obj W] η.app W (b ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] n)) =
        (S.map (M.val ◁ η)).val.app W
          ((adj.unit.app (M.val ⊗ E)).app W
            (m ⊗ₜ[B.obj.obj W] (b ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] n))) at he
      change f.val.app W ((tensorObjIsoSheafification M (S.obj E)).inv.val.app W
          ((S.map (M.val ◁ η)).val.app W ((adj.unit.app (M.val ⊗ E)).app W
            (m ⊗ₜ[B.obj.obj W] (b ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] n))))) =
        g.val.app W ((tensorObjIsoSheafification M (S.obj E)).inv.val.app W
          ((S.map (M.val ◁ η)).val.app W ((adj.unit.app (M.val ⊗ E)).app W
            (m ⊗ₜ[B.obj.obj W] (b ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] n)))))
      rw [← he]
      exact h W m b n

end SheafOfModules
