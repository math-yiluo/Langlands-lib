/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Descent of a compatible finite-stage adjunction

Source: blueprint `thm-coef-qbar-verdier`, proof steps 6--8. Compatible units and
counits descend as natural transformations. Their triangle identities are checked
on the object at its own stage, so no separate Hom-colimit construction is needed.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w u v u' v'

namespace CategoryTheory.StageSystem.Morphism

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)]
  {S : StageSystem C} {T : StageSystem D}
  (F : S.Morphism T) (G : T.Morphism S)
  (a : ∀ i, F.Φ i ⊣ G.Φ i)
  (unit : Hom (id S) (F.comp G))
  (counit : Hom (G.comp F) (id T))
  (unit_eq : ∀ i, unit.τ i = (a i).unit)
  (counit_eq : ∀ i, counit.τ i = (a i).counit)

/-- A stage-compatible adjunction descends with its actual finite unit and counit.
Source: blueprint `thm-coef-qbar-verdier`, proof steps 6--8
(blueprint: lem-coef-qbar-stage-adjunction-descent).

Proof: descend the two compatible families using `descNatTrans`, and conjugate by
the canonical identity and composition comparisons. These comparisons have identity
components. At a pair `(i,x)` the left triangle is the inclusion of the left triangle
of `a i`; the right triangle is its right triangle. Functoriality of inclusion proves
both equations. This includes repeated stages and requires neither full faithfulness
of the inclusions nor faithfulness of a scalar transition. -/
def adjunction : F.functor ⊣ G.functor where
  unit := (functorIdIso (S := S)).inv ≫ descNatTrans unit ≫ (functorCompIso F G).hom
  counit := (functorCompIso G F).inv ≫ descNatTrans counit ≫
    (functorIdIso (S := T)).hom
  left_triangle_components X := by
    simp only [NatTrans.comp_app, functorIdIso_inv_app, functorCompIso_hom_app,
      functorCompIso_inv_app, functorIdIso_hom_app, Category.id_comp, Category.comp_id,
      descNatTrans_app, unit_eq, counit_eq]
    rw [functor_map_ι]
    change (T.ι X.stage).map ((F.Φ X.stage).map ((a X.stage).unit.app X.obj)) ≫
      (T.ι X.stage).map ((a X.stage).counit.app ((F.Φ X.stage).obj X.obj)) = 𝟙 _
    calc
      _ = (T.ι X.stage).map
          ((F.Φ X.stage).map ((a X.stage).unit.app X.obj) ≫
            (a X.stage).counit.app ((F.Φ X.stage).obj X.obj)) :=
        ((T.ι X.stage).map_comp _ _).symm
      _ = (T.ι X.stage).map (𝟙 _) :=
        congrArg (fun q ↦ (T.ι X.stage).map q) ((a X.stage).left_triangle_components X.obj)
      _ = 𝟙 _ := (T.ι X.stage).map_id _
  right_triangle_components X := by
    simp only [NatTrans.comp_app, functorIdIso_inv_app, functorCompIso_hom_app,
      functorCompIso_inv_app, functorIdIso_hom_app, Category.id_comp, Category.comp_id,
      descNatTrans_app, unit_eq, counit_eq]
    rw [functor_map_ι]
    change (S.ι X.stage).map ((a X.stage).unit.app ((G.Φ X.stage).obj X.obj)) ≫
      (S.ι X.stage).map ((G.Φ X.stage).map ((a X.stage).counit.app X.obj)) = 𝟙 _
    calc
      _ = (S.ι X.stage).map
          ((a X.stage).unit.app ((G.Φ X.stage).obj X.obj) ≫
            (G.Φ X.stage).map ((a X.stage).counit.app X.obj)) :=
        ((S.ι X.stage).map_comp _ _).symm
      _ = (S.ι X.stage).map (𝟙 _) :=
        congrArg (fun q ↦ (S.ι X.stage).map q) ((a X.stage).right_triangle_components X.obj)
      _ = 𝟙 _ := (S.ι X.stage).map_id _

/-- The descended unit retains its specified finite component.
Source: blueprint thm-coef-qbar-verdier, proof step 8
(blueprint: lem-coef-qbar-stage-adjunction-descent). -/
theorem adjunction_unit_app (X : S.PairCategory) :
    (adjunction F G a unit counit unit_eq counit_eq).unit.app X =
      (S.ι X.stage).map ((a X.stage).unit.app X.obj) := by
  change (functorIdIso (S := S)).inv.app X ≫
      (descNatTrans unit).app X ≫ (functorCompIso F G).hom.app X = _
  simp only [functorIdIso_inv_app, functorCompIso_hom_app, Category.id_comp,
    Category.comp_id, descNatTrans_app, unit_eq]

/-- The descended counit retains its specified finite component.
Source: blueprint thm-coef-qbar-verdier, proof step 8
(blueprint: lem-coef-qbar-stage-adjunction-descent). -/
theorem adjunction_counit_app (X : T.PairCategory) :
    (adjunction F G a unit counit unit_eq counit_eq).counit.app X =
      (T.ι X.stage).map ((a X.stage).counit.app X.obj) := by
  change (functorCompIso G F).inv.app X ≫
      (descNatTrans counit).app X ≫ (functorIdIso (S := T)).hom.app X = _
  simp only [functorCompIso_inv_app, functorIdIso_hom_app, Category.id_comp,
    Category.comp_id, descNatTrans_app, counit_eq]

end CategoryTheory.StageSystem.Morphism
