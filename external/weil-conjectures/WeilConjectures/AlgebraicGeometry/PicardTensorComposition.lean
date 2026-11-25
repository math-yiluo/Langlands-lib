/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardCanonicalBaseChange
import WeilConjectures.AlgebraicGeometry.PullbackTensorComposition

/-! # Composition coherence for Picard pullback comparisons

Source: Stacks Project, Tags 0095 and 0096.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse tensor comparison respects pullback composition.
Source: Stacks Project, Definition 6.26.1(2), Tag 0095; Lemma 6.26.2, Tag 0096.
(blueprint: lem-sc-picard-tensor-composition)

Proof: Expand picardTensorObjIso and picardTensorCompIso into the ordinary
pullback tensorator and the comparisons picardTensorComparison. Combine the
successive functor maps, then cancel the inner comparison inverse followed by
its hom. Combine the two tensor morphisms on the right and cancel the composite
comparison inverse followed by its hom in both arguments. Naturality of the
comparison for k moves the map of the inner tensorator across the comparison;
its inverse and hom cancel. Naturality of the ordinary tensorator moves the
pair of comparisons for l before that tensorator. Naturality of the comparison
for k in each argument then identifies these maps with the two functor maps of
the comparisons for l. Apply ordinary pullbackComp_tensor to the remaining
ordinary tensorators and composition comparison. Tensor functoriality and
associativity identify the result with the expanded right side. No pairing or
unit map is used; zero modules and empty schemes satisfy the same equations. -/
@[reassoc]
theorem picardTensorObjIso_comp_inv
    {X Y Z : Scheme.{u}} (k : Z ⟶ Y) (l : Y ⟶ X) (M N : X.Modules) :
    (picardTensorObjIso k ((tensorPullback l).obj M) ((tensorPullback l).obj N)).inv ≫
      (tensorPullback k).map (picardTensorObjIso l M N).inv ≫
        (picardTensorCompIso k l (M ⊗ N)).hom =
    ((picardTensorCompIso k l M).hom ⊗ₘ (picardTensorCompIso k l N).hom) ≫
      (picardTensorObjIso (k ≫ l) M N).inv := by
  simp only [picardTensorObjIso, picardTensorCompIso, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_inv, Iso.symm_hom, tensorIso_inv, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc]
  simp only [Iso.app_inv]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [(picardTensorComparison k).hom.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc, Functor.map_comp, Category.assoc]
  simp only [Functor.Monoidal.μIso_hom]
  rw [← Functor.LaxMonoidal.μ_natural_assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  erw [← (picardTensorComparison k).hom.naturality
      ((picardTensorComparison l).hom.app M),
    ← (picardTensorComparison k).hom.naturality ((picardTensorComparison l).hom.app N)]
  rw [← tensorHom_comp_tensorHom_assoc]
  have hc := pullbackComp_tensor_assoc k l M N
    ((picardTensorComparison (k ≫ l)).inv.app (M ⊗ N))
  simp only [Functor.Monoidal.μIso_hom] at hc
  rw [hc]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc]

end AlgebraicGeometry.Scheme.Modules
