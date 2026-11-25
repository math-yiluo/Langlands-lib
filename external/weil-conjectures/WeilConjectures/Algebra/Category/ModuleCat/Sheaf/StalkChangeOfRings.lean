/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkChangeOfRingsPresheaf
import Mathlib.Topology.Sheaves.Sheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-!
# Stalks of change of rings

Source: Stacks Project, Sheaves, Lemma 008B, from Lemmas 007K and 007Z
(blueprint: lem-weil-pbc-stalk-change-of-rings-tensor).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite TopCat.Presheaf
open scoped ChangeOfRings

namespace SheafOfModules

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private theorem stalkAddMap_germ {X : TopCat.{u}}
    {R : TopCat.Presheaf RingCat.{u} X} {x : X}
    {M N : PresheafOfModules.{u} R} (f : M ⟶ N)
    (U : Opens X) (hx : x ∈ U) (s : M.obj (op U)) :
    PresheafOfModules.stalkAddMap f (germ M.presheaf U x hx s) =
      germ N.presheaf U x hx (f.app (op U) s) := by
  exact stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf R).map f) s

private theorem stalkAddMap_comm_smul {X : TopCat.{u}}
    (R : TopCat.Presheaf CommRingCat.{u} X) {x : X}
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ N)
    (r : R.stalk x) (m : stalk (C := Ab.{u}) M.presheaf x) :
    PresheafOfModules.stalkAddMap f (r • m) = r • PresheafOfModules.stalkAddMap f m := by
  obtain ⟨U, hxU, r, rfl⟩ := R.exists_germ_eq r
  obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← R.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx r,
    ← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx m,
    ← PresheafOfModules.germ_smul (R := R) M]
  rw [stalkAddMap_germ, map_smul, PresheafOfModules.germ_smul (R := R) N,
    stalkAddMap_germ]

private theorem stalk_sheafification_bijective {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)
    (P : PresheafOfModules.{u} R.obj) :
    Function.Bijective (PresheafOfModules.stalkAddMap (x := x)
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P)) := by
  let t := (stalkFunctor Ab.{u} x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf)
  let : IsIso t := stalkFunctor_map_unit_toSheafify_isIso x Ab.{u} P.presheaf
  change Function.Bijective t
  exact ConcreteCategory.bijective_of_isIso t

private theorem stalkSheafification_unit_app_naturality {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {P Q : PresheafOfModules.{u} R.obj} (f : P ⟶ Q)
    (U : Opens X) (s : P.obj (op U)) :
    ((PresheafOfModules.sheafification (𝟙 R.obj)).map f).val.app (op U)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P).app (op U) s) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app Q).app (op U)
        (f.app (op U) s) := by
  have h := congrArg (fun t ↦ t.app (op U))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.naturality f)
  exact (ConcreteCategory.congr_hom h s).symm

/-- Change of rings commutes with stalks, naturally in the module and compatibly with germs.
Mathlib writes extension of scalars with the coefficient factor first: `a ⊗ s`
represents the paper's `s ⊗ a` under the canonical tensor commutation.
Source: Stacks Project, Sheaves, Lemma 008B
(blueprint: lem-weil-pbc-stalk-change-of-rings-tensor).

Proof:
1. On neighborhoods of `x`, take the section rings and module sections with their
   semilinear restrictions (`def-weil-pbc-module-stalk`). The ring morphism induces
   the stalk ring morphism and hence the scalar action on the changed stalk module.
2. The sheafification unit induces an additive stalk isomorphism
   (`def-weil-presheaf-modules-sheafification`, `lem-weil-pbc-stalk-sheafification-space`).
   Represent a scalar and a vector on a common neighborhood to check linearity.
3. Apply `lem-weil-pbc-filtered-colimit-tensor-varying-rings` to these neighborhood
   systems. It identifies the presheaf change-of-rings stalk with the tensor of stalks.
   Check linearity over the target stalk ring on pure tensor germs, which generate.
4. Compose the inverse of that identification with the sheafification stalk map.
   This gives the displayed isomorphism and pure-tensor germ formula.
5. Both naturality composites send `a_x ⊗ s_x` to the germ of `a ⊗ f(s)`.
   Generation by pure tensor germs gives equality. -/
theorem stalkChangeOfRingsIso (X : TopCat.{u})
    (R₁ R₂ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (α : R₁ ⟶ R₂) (x : X) :
    ∃ Φ : ∀ F : SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁),
      (ModuleCat.extendScalars ((TopCat.Presheaf.stalkFunctor CommRingCat x).map α.hom).hom).obj
        (ModuleCat.of (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) R₁.obj x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) F.val.presheaf x)) ≅
      ModuleCat.of (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) R₂.obj x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) (changeOfRings α F).val.presheaf x),
      (∀ (F : SheafOfModules.{u}
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁))
        (U : Opens X) (hx : x ∈ U) (s : F.val.obj (op U)) (a : R₂.obj.obj (op U)),
        (Φ F).hom
          (TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := X) R₂.obj U x hx a
          ⊗ₜ[TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) R₁.obj x,
            ((TopCat.Presheaf.stalkFunctor CommRingCat x).map α.hom).hom]
            TopCat.Presheaf.germ (C := Ab.{u}) (X := X) F.val.presheaf U x hx s) =
          TopCat.Presheaf.germ (C := Ab.{u}) (X := X) (changeOfRings α F).val.presheaf U x hx
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 ((sheafCompose (Opens.grothendieckTopology X)
                (forget₂ CommRingCat.{u} RingCat.{u})).obj R₂).obj)).unit.app
                  (changeOfRingsPresheaf.{u, u, u} α F)).app (op U)
              (a ⊗ₜ[R₁.obj.obj (op U), (α.hom.app (op U)).hom] s))) ∧
      (∀ (F G : SheafOfModules.{u}
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁)) (f : F ⟶ G)
        (a : TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) R₂.obj x)
        (s : TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) F.val.presheaf x),
        PresheafOfModules.stalkAddMap (x := x) (changeOfRingsHom α F f).val
          ((Φ F).hom
            (a ⊗ₜ[TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) R₁.obj x,
              ((TopCat.Presheaf.stalkFunctor CommRingCat x).map α.hom).hom] s)) =
          (Φ G).hom
            (a ⊗ₜ[TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) R₁.obj x,
              ((TopCat.Presheaf.stalkFunctor CommRingCat x).map α.hom).hom]
              PresheafOfModules.stalkAddMap (x := x) f.val s)) := by
  classical
  obtain ⟨Ψ, hΨ⟩ := stalkChangeOfRingsPresheafIso X R₁ R₂ α x
  let R := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R₂
  let θ (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁)) :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app
      (changeOfRingsPresheaf.{u, u, u} α F)
  let L (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁)) :
      stalk (C := Ab.{u}) (changeOfRingsPresheaf.{u, u, u} α F).presheaf x
        →ₗ[stalk (C := CommRingCat.{u}) R₂.obj x]
        stalk (C := Ab.{u}) (changeOfRings α F).val.presheaf x :=
    { toFun := PresheafOfModules.stalkAddMap (θ F)
      map_add' := (PresheafOfModules.stalkAddMap (θ F)).map_add
      map_smul' := stalkAddMap_comm_smul R₂.obj (θ F) }
  let E (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁)) :=
    (LinearEquiv.ofBijective (L F)
      (stalk_sheafification_bijective R x (changeOfRingsPresheaf.{u, u, u} α F))).toModuleIso
  let Φ := fun F ↦ Ψ F ≪≫ E F
  have hΦ : ∀ (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁))
      (U : Opens X) (hx : x ∈ U) (s : F.val.obj (op U)) (a : R₂.obj.obj (op U)),
      (Φ F).hom
        (germ R₂.obj U x hx a
          ⊗ₜ[stalk (C := CommRingCat.{u}) R₁.obj x, ((stalkFunctor CommRingCat x).map α.hom).hom]
          germ F.val.presheaf U x hx s) =
        germ (changeOfRings α F).val.presheaf U x hx
          ((θ F).app (op U) (a ⊗ₜ[R₁.obj.obj (op U), (α.hom.app (op U)).hom] s)) := by
    intro F U hx s a
    change PresheafOfModules.stalkAddMap (θ F) ((Ψ F).hom _) = _
    rw [hΨ F U hx s a]
    exact stalkAddMap_germ (θ F) U hx _
  refine ⟨Φ, hΦ, ?_⟩
  intro F G f a s
  obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := CommRingCat.{u}) R₂.obj a
  obtain ⟨V, hxV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf s
  have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← TopCat.Presheaf.germ_res_apply R₂.obj (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx a,
    ← TopCat.Presheaf.germ_res_apply F.val.presheaf (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx s,
    hΦ]
  erw [stalkAddMap_germ (changeOfRingsHom α F f).val,
    stalkAddMap_germ f.val]
  rw [hΦ]
  let k : changeOfRingsPresheaf.{u, u, u} α F ⟶
      changeOfRingsPresheaf.{u, u, u} α G :=
    { app := fun W ↦ (ModuleCat.extendScalars (α.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturality α F f }
  apply congrArg (germ (changeOfRings α G).val.presheaf (U ⊓ V) x hx)
  exact stalkSheafification_unit_app_naturality R k (U ⊓ V) _

end SheafOfModules
