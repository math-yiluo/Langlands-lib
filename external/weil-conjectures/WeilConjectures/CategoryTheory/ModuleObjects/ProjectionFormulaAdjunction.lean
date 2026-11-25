/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula

/-!

# The unit and counit of the linearized adjunction

Let `adj : P ⊣ S` be an adjunction with `S` strong monoidal satisfying the projection formula,
and `B` an algebra object. The linearized adjunction
`Adjunction.mapModLeftAdjunction : adj.mapModLeft B ⊣ S.mapMod B` of
`WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula` has as unit and counit the
unit and counit of `adj` on the underlying objects. Consequently, the linearization of `P` is
fully faithful if `P` is, and a module object over `B` lies in the essential image of the
linearization as soon as its underlying object lies in the essential image of `P`.

## Main results

- `Adjunction.mapModLeftAdjunction_unit_app_hom`, `Adjunction.mapModLeftAdjunction_counit_app_hom`:
  the unit and counit of the linearized adjunction.
- `Adjunction.fullyFaithfulMapModLeft`: the linearization of a fully faithful `P` is fully
  faithful.
- `Adjunction.mapModLeft_essImage_of_essImage`: a module object whose underlying object lies in
  the essential image of `P` lies in the essential image of the linearization of `P`.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {P : C ⥤ D} {S : D ⥤ C} (adj : P ⊣ S) [S.Monoidal] [adj.HasProjectionFormula]
  {B : D} [MonObj B]

/-- The unit of the linearized adjunction `adj.mapModLeft B ⊣ S.mapMod B` is the unit of `adj`
on the underlying objects. -/
lemma mapModLeftAdjunction_unit_app_hom (M : Mod C (S.obj B)) :
    ((adj.mapModLeftAdjunction (B := B)).unit.app M).hom = adj.unit.app M.X :=
  adj.homEquiv_id M.X

/-- The counit of the linearized adjunction `adj.mapModLeft B ⊣ S.mapMod B` is the counit of
`adj` on the underlying objects. -/
lemma mapModLeftAdjunction_counit_app_hom (N : Mod D B) :
    ((adj.mapModLeftAdjunction (B := B)).counit.app N).hom = adj.counit.app N.X :=
  adj.homEquiv_symm_id N.X

/-- The unit of the linearized adjunction is an isomorphism if the unit of `adj` is. -/
instance isIso_mapModLeftAdjunction_unit [IsIso adj.unit] :
    IsIso (adj.mapModLeftAdjunction (B := B)).unit := by
  have (M : Mod C (S.obj B)) : IsIso ((adj.mapModLeftAdjunction (B := B)).unit.app M) := by
    have : IsIso ((Mod.forget _).map ((adj.mapModLeftAdjunction (B := B)).unit.app M)) := by
      rw [Mod.forget_map, mapModLeftAdjunction_unit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  exact NatIso.isIso_of_isIso_app _

/-- The linearization `adj.mapModLeft B` of a fully faithful left adjoint `P` is fully
faithful. -/
noncomputable def fullyFaithfulMapModLeft [P.Full] [P.Faithful] :
    (adj.mapModLeft B).FullyFaithful :=
  (adj.mapModLeftAdjunction (B := B)).fullyFaithfulLOfIsIsoUnit

/-- If `P` is fully faithful, a module object over `B` whose underlying object lies in the
essential image of `P` lies in the essential image of the linearization `adj.mapModLeft B`. -/
lemma mapModLeft_essImage_of_essImage [P.Full] [P.Faithful] (N : Mod D B)
    (hN : P.essImage N.X) : (adj.mapModLeft B).essImage N := by
  have : IsIso ((Mod.forget B).map ((adj.mapModLeftAdjunction (B := B)).counit.app N)) := by
    rw [Mod.forget_map, mapModLeftAdjunction_counit_app_hom,
      isIso_counit_app_iff_mem_essImage]
    exact hN
  have := isIso_of_reflects_iso ((adj.mapModLeftAdjunction (B := B)).counit.app N)
    (Mod.forget B)
  exact (adj.mapModLeftAdjunction (B := B)).mem_essImage_of_counit_isIso N

end CategoryTheory.Adjunction
