/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.InternalHomOverEquiv
import WeilConjectures.Algebra.Homology.InternalHomOverNaturality

/-! # Internal Hom and open restriction on schemes

Source: Stacks Project, Cohomology, Tag 08DL.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Internal Hom commutes with open restriction, compatibly with both compositions.
Source: Stacks Project, Cohomology, Tag 08DL, ordinary internal Hom restriction.
(blueprint: lem-sc-internal-hom-restrict-scheme)

Proof: First restrict to the over-U site with `overHomObjIso`, which identifies
local linear maps on its iterated slices. Apply the functor of `overEquiv U` and
then `internalHom_overEquiv` to identify internal Homs on the open subscheme.
The natural isomorphism `overFunctorEquiv U` identifies this composite restriction
with `restrictFunctor U.ι`. Conjugate both arguments of internal Hom by its
components, using the inverse on the source and the forward map on the target.
The resulting composites are isomorphisms. Naturality follows by composing the
naturality equations for `overHomObjIso`, `internalHom_overEquiv`, and
`overFunctorEquiv`: the intermediate conjugating maps cancel. This argument
also applies to the empty open and zero sheaves; it uses no finiteness assumptions. -/
theorem internalHom_restrict_scheme {Y : Scheme.{u}} (U : Y.Opens) :
    let F := Scheme.Modules.restrictFunctor U.ι
    ∃ s : ∀ A B : Y.Modules,
      F.obj (SheafOfModules.homObj (R := Y.toRingedSpace.sheaf) A B) ≅
        SheafOfModules.homObj (R := U.toScheme.toRingedSpace.sheaf) (F.obj A) (F.obj B),
      ∀ {A A' B B'} (f : A' ⟶ A) (g : B ⟶ B'),
        F.map (SheafOfModules.homObjMap (R := Y.toRingedSpace.sheaf) f g) ≫
            (s A' B').hom =
          (s A B).hom ≫ SheafOfModules.homObjMap
            (R := U.toScheme.toRingedSpace.sheaf) (F.map f) (F.map g) := by
  classical
  intro F
  let O := SheafOfModules.overFunctor.{u} Y.ringCatSheaf U
  let T := (Scheme.Modules.overEquiv U).functor
  let t := Scheme.Modules.overFunctorEquiv U
  obtain ⟨a, ha⟩ := internalHom_overEquiv U
  let b (A B : Y.Modules) :
      SheafOfModules.homObj (R := U.toScheme.toRingedSpace.sheaf)
        (T.obj (O.obj A)) (T.obj (O.obj B)) ≅
      SheafOfModules.homObj (R := U.toScheme.toRingedSpace.sheaf) (F.obj A) (F.obj B) :=
    { hom := SheafOfModules.homObjMap (R := U.toScheme.toRingedSpace.sheaf)
        (t.app A).inv (t.app B).hom
      inv := SheafOfModules.homObjMap (R := U.toScheme.toRingedSpace.sheaf)
        (t.app A).hom (t.app B).inv
      hom_inv_id := by
        simp only [SheafOfModules.homObjMap_comp_homObjMap, Iso.hom_inv_id]
        exact SheafOfModules.homObjMap_id (R := U.toScheme.toRingedSpace.sheaf)
      inv_hom_id := by
        simp only [SheafOfModules.homObjMap_comp_homObjMap, Iso.inv_hom_id]
        exact SheafOfModules.homObjMap_id (R := U.toScheme.toRingedSpace.sheaf) }
  let s (A B : Y.Modules) := (t.app (SheafOfModules.homObj
      (R := Y.toRingedSpace.sheaf) A B)).symm ≪≫
    T.mapIso (SheafOfModules.overHomObjIso A B U) ≪≫ a (O.obj A) (O.obj B) ≪≫ b A B
  refine ⟨s, ?_⟩
  intro A A' B B' f g
  have h₁ := t.inv.naturality (SheafOfModules.homObjMap
    (R := Y.toRingedSpace.sheaf) f g)
  change F.map (SheafOfModules.homObjMap (R := Y.toRingedSpace.sheaf) f g) ≫
      (t.app _).inv = (t.app _).inv ≫ T.map (O.map _) at h₁
  have h₂ := congrArg T.map (overHomObjIso_naturality (R := Y.toRingedSpace.sheaf) U f g)
  have h₃ := ha (O.obj A) (O.obj A') (O.obj B) (O.obj B') (O.map f) (O.map g)
  have h₄ : SheafOfModules.homObjMap (R := U.toScheme.toRingedSpace.sheaf)
      (T.map (O.map f)) (T.map (O.map g)) ≫ (b A' B').hom =
      (b A B).hom ≫ SheafOfModules.homObjMap
        (R := U.toScheme.toRingedSpace.sheaf) (F.map f) (F.map g) := by
    dsimp only [b]
    simp only [SheafOfModules.homObjMap_comp_homObjMap]
    congr 1
  change F.map _ ≫ ((t.app _).inv ≫ T.map _ ≫ (a _ _).hom ≫ (b A' B').hom) =
    ((t.app _).inv ≫ T.map _ ≫ (a _ _).hom ≫ (b A B).hom) ≫ _
  simp only [Functor.map_comp] at h₂
  rw [← Category.assoc, h₁, Category.assoc, ← Category.assoc (T.map (O.map (SheafOfModules.homObjMap
      (R := Y.toRingedSpace.sheaf) f g))), h₂,
    Category.assoc, ← Category.assoc (T.map (SheafOfModules.homObjMap
      (R := Y.toRingedSpace.sheaf.over U) (O.map f) (O.map g))), h₃,
    Category.assoc, h₄]
  simp only [Category.assoc]


end AlgebraicGeometry
