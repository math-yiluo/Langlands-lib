/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardCanonicalBaseChange
import WeilConjectures.AlgebraicGeometry.PicardTensorComposition
import WeilConjectures.AlgebraicGeometry.PicardUnitComposition

/-! # Composition of pulled pairings

Source: Stacks Project, Tag 0095, tensor formula; Tag 0096, adjunction.
(blueprint: lem-sc-picard-pairing-composition).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
private theorem picardTensorCompIso_naturality
    {X Y Z : Scheme.{u}} (k : Z ⟶ Y) (l : Y ⟶ X)
    {A B : X.Modules} (f : A ⟶ B) :
    (picardTensorCompIso k l A).hom ≫ (tensorPullback (k ≫ l)).map f =
      (tensorPullback k).map ((tensorPullback l).map f) ≫
        (picardTensorCompIso k l B).hom := by
  let c : tensorPullback l ⋙ tensorPullback k ≅ tensorPullback (k ≫ l) :=
    Functor.isoWhiskerRight (picardTensorComparison l) (tensorPullback k) ≪≫
      Functor.isoWhiskerLeft (pullback l) (picardTensorComparison k) ≪≫
        pullbackComp k l ≪≫ (picardTensorComparison (k ≫ l)).symm
  exact (c.hom.naturality f).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pulling a pairing twice agrees with pulling it along the composite, after the
specified composition comparison on each argument.
Source: Stacks Project, Tag 0095, tensor formula; Tag 0096, adjunction.
(blueprint: lem-sc-picard-pairing-composition)

Proof: Eliminate e, making t definitionally k followed by l and the two
object-equality comparisons identities. Expand functoriality of tensorPullback k
on the inner pairing. The proved unit-composition identity replaces the two unit
maps by the composition comparison at O_X followed by the composite unit map.
The composition comparison is a natural isomorphism: whisker the comparisons
picardTensorComparison l and picardTensorComparison k, then compose with
ordinary pullbackComp and the inverse comparison at k followed by l. Its
naturality at g moves the composition comparison from O_X to M tensor N.
The tensor-composition identity then replaces the two tensorators followed by
this comparison with the tensor of the two argument comparisons followed by
the composite tensorator. This is exactly the requested formula. The tensor
identity is proved by transporting ordinary pullbackComp_tensor; the unit
identity is proved independently from pullback sections and their composition.
No finiteness, flatness or invertibility of g is used. Zero pairings, zero
modules, empty schemes and identity arrows satisfy these same categorical laws. -/
theorem picardPairing_comp
    {X Y Z : Scheme.{u}} (k : Z ⟶ Y) (l : Y ⟶ X) (t : Z ⟶ X)
    (e : k ≫ l = t) (M N : X.Modules)
    (g : M ⊗ N ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (picardTensorObjIso k ((tensorPullback l).obj M) ((tensorPullback l).obj N)).inv ≫
      (tensorPullback k).map
        ((picardTensorObjIso l M N).inv ≫ (tensorPullback l).map g ≫
          (picardTensorUnitIso l).hom) ≫ (picardTensorUnitIso k).hom =
    (((picardTensorCompIso k l M).hom ≫
        (eqToIso (congrArg (fun s ↦ (tensorPullback s).obj M) e)).hom) ⊗ₘ
      ((picardTensorCompIso k l N).hom ≫
        (eqToIso (congrArg (fun s ↦ (tensorPullback s).obj N) e)).hom)) ≫
      (picardTensorObjIso t M N).inv ≫ (tensorPullback t).map g ≫
        (picardTensorUnitIso t).hom := by
  subst t
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [picardTensorUnitIso_comp]
  rw [← picardTensorCompIso_naturality_assoc]
  rw [picardTensorObjIso_comp_inv_assoc]

end AlgebraicGeometry.Scheme.Modules
