/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor

/-! # Tensor projection under a specified right-adjoint comparison -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory MonoidalCategory
namespace CategoryTheory.Adjunction

/-- Transporting a right adjoint transports the unit-defined projection by its mixed
comparison. Source: adjunction Hom bijections and Stacks Tag 0GL1
(blueprint: lem-pur-tensor-projection-right-transport).

Proof: express both projection components as inverse Hom transposes. For the
transported adjunction its unit is the original unit followed by the inverse right
comparison. Its inverse Hom transpose appends the forward right comparison. Tensor
bifunctoriality therefore gives exactly the mixed comparison in the statement. -/
theorem tensorProjection_ofNatIsoRight
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {J : C ⥤ D} {Q U : D ⥤ C} (adj : J ⊣ Q) [U.Monoidal]
    (s : U ≅ Q)
    (δ : (((Functor.whiskeringLeft₂ C).obj Q).obj U).obj (curriedTensor C) ⟶
      (Functor.postcompose₂.obj Q).obj (curriedTensor D))
    (hδ : ∀ M H : D, (δ.app M).app H =
      s.inv.app M ▷ U.obj H ≫ Functor.LaxMonoidal.μ U M H ≫ s.hom.app (M ⊗ H))
    (M : C) (H : D) :
    (((adj.ofNatIsoRight s.symm).projectionMap U (curriedTensor C) (curriedTensor D)
      (Functor.LaxMonoidal.μNatTrans U)).app M).app H =
      ((adj.projectionMap U (curriedTensor C) (curriedTensor D) δ).app M).app H := by
  rw [projectionMap_app_app, projectionMap_app_app,
    homEquiv_ofNatIsoRight_symm_apply]
  apply congrArg (adj.homEquiv _ _).symm
  change ((adj.ofNatIsoRight s.symm).unit.app M ▷ U.obj H ≫
      Functor.LaxMonoidal.μ U (J.obj M) H) ≫ s.hom.app _ =
    adj.unit.app M ▷ U.obj H ≫ (δ.app (J.obj M)).app H
  rw [hδ]
  simp only [ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_hom, comp_whiskerRight, Category.assoc]

end CategoryTheory.Adjunction
