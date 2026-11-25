/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.AlgebraicGeometry.ProEtaleStructureSheaf
import WeilConjectures.Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-! # Units of the pro-etale structure sheaf

Source: Stacks Project, Tags 03PK and 03O3 (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The units presheaf, written additively and lifted to the ambient sheaf universe.
Source: Stacks Project, Tag 03PK (auxiliary; not a blueprint node).
Its sections are `ULift (Additive Γ(U, O_U)ˣ)`; addition means multiplication of units. -/
def proEtaleUnitsPresheaf (S : Scheme.{u}) : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (proEtaleStructureSheaf S).obj ⋙ forget₂ CommRingCat CommMonCat ⋙
    CommMonCat.units ⋙ CommGrpCat.toAddCommGrp ⋙ AddCommGrpCat.uliftFunctor.{u + 1}

/-- Units satisfy descent on the pro-etale site.
Source: Stacks Project, Tags 03PK and 03O3 (auxiliary; not a blueprint node).
Proof: glue a compatible family of units in the structure sheaf, and separately glue its
inverses. The two glued sections multiply to one, since they do on a covering. Thus the
glued section is a unit. Uniqueness follows from uniqueness for the structure sheaf.
Changing multiplicative notation to additive notation and lifting universes preserve descent. -/
theorem proEtaleUnitsPresheaf_isSheaf (S : Scheme.{u}) :
    Presheaf.IsSheaf (ProEt.topology S) (proEtaleUnitsPresheaf S) := by
  exact Presheaf.isSheaf_comp_of_isSheaf (ProEt.topology S)
    (proEtaleStructureSheaf S).obj
    (forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
      CommGrpCat.toAddCommGrp ⋙ AddCommGrpCat.uliftFunctor.{u + 1})
    (proEtaleStructureSheaf S).property

/-- The sheaf `G_m = O_Sˣ` of abelian groups on the small pro-etale site.
Source: Stacks Project, Tag 03PK (auxiliary; not a blueprint node). -/
def proEtaleUnitsSheaf (S : Scheme.{u}) : Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1} :=
  ⟨proEtaleUnitsPresheaf S, proEtaleUnitsPresheaf_isSheaf S⟩

end AlgebraicGeometry.Scheme
