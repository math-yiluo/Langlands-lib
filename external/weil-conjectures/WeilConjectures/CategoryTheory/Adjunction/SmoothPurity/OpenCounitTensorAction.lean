/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.UnitAdjunctTensorAction

/-! # Tensor linearity of an open-extension counit -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory MonoidalCategory
namespace CategoryTheory.Adjunction

/-- The symmetry-conjugate inverse open projection satisfies the counit square.
Source: Stacks Tag 0GL1, extension by zero and tensor
(blueprint: lem-pur-open-counit-tensor-action).

Proof: the unit-defined right-coefficient projection satisfies the counit equation
by transposition and the right triangle identity. Braidedness moves the swap through
the tensorator, and counit naturality moves the resulting mapped swap past the
counit. The inverse projection cancels and symmetry naturality gives the claimed
left-coefficient equation. -/
theorem openCounit_tensorAction
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalCategory D] [SymmetricCategory D]
    {J : C ⥤ D} {Q : D ⥤ C} (adj : J ⊣ Q) [Q.Braided]
    (H M : D)
    [IsIso (((adj.projectionMap Q (curriedTensor C) (curriedTensor D)
      (Functor.LaxMonoidal.μNatTrans Q)).app (Q.obj M)).app H)] :
    (β_ H (J.obj (Q.obj M))).hom ≫
      inv (((adj.projectionMap Q (curriedTensor C) (curriedTensor D)
        (Functor.LaxMonoidal.μNatTrans Q)).app (Q.obj M)).app H) ≫
      J.map (β_ (Q.obj M) (Q.obj H)).hom ≫
      J.map (Functor.LaxMonoidal.μ Q H M) ≫ adj.counit.app (H ⊗ M) =
        H ◁ adj.counit.app M := by
  have hμ : (β_ (Q.obj M) (Q.obj H)).hom ≫ Functor.LaxMonoidal.μ Q H M =
      Functor.LaxMonoidal.μ Q M H ≫ Q.map (β_ M H).hom :=
    (Functor.LaxBraided.braided (F := Q) M H).symm
  have hn := adj.counit.naturality (β_ M H).hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [← J.map_comp_assoc, hμ, J.map_comp, Category.assoc, hn]
  have hc := (unitAdjunctTensorAction adj).2.2 M H
  rw [reassoc_of% hc, IsIso.inv_hom_id_assoc]
  rw [← BraidedCategory.braiding_naturality_assoc]
  simp only [id_tensorHom]
  rw [SymmetricCategory.symmetry, Category.comp_id]

end CategoryTheory.Adjunction
