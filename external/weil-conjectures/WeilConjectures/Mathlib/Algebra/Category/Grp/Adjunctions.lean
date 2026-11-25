/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.Ring.Constructions
public import WeilConjectures.Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-!
# The group of units of a commutative ring, as a functor

Mathlib has the functor `CommMonCat.units` sending a commutative monoid to its group of
units, and shows that it is a right adjoint. Composing it with the forgetful functor from
commutative rings gives the functor of units of a commutative ring

```
  CommRingCat ──forget₂──▶ CommMonCat ──CommMonCat.units──▶ CommGrpCat
```

and composing further with the equivalence `CommGrpCat.toAddCommGrp` writes the group of
units additively. All three functors are right adjoints, so the composites preserve limits;
this is what makes the presheaf of units of a sheaf of rings a sheaf.

## Main definitions

- `CommRingCat.units`: the functor `R ↦ Rˣ` from commutative rings to commutative groups.
- `CommRingCat.unitsAddCommGrp`: the same functor with `Rˣ` written additively.
- `CommRingCat.unitsAddCommGrpULift`: the same functor followed by a universe lift.
-/

@[expose] public section

universe v v' u

open CategoryTheory Limits

namespace CommRingCat

/-- The functor sending a commutative ring to its group of units,

```
  CommRingCat ──forget₂──▶ CommMonCat ──CommMonCat.units──▶ CommGrpCat
```
-/
noncomputable def units : CommRingCat.{u} ⥤ CommGrpCat.{u} :=
  forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units

@[simp] lemma units_obj (R : CommRingCat.{u}) : units.obj R = CommGrpCat.of Rˣ := rfl

noncomputable instance : PreservesLimitsOfSize.{v, v'} units.{u} := by
  unfold units; infer_instance

/-- The functor sending a commutative ring to its group of units, written additively:
`CommRingCat.units` followed by the equivalence `CommGrpCat.toAddCommGrp`. -/
noncomputable def unitsAddCommGrp : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  units ⋙ CommGrpCat.toAddCommGrp

@[simp] lemma unitsAddCommGrp_obj (R : CommRingCat.{u}) :
    unitsAddCommGrp.obj R = AddCommGrpCat.of (Additive Rˣ) :=
  rfl

noncomputable instance : PreservesLimitsOfSize.{v, v'} unitsAddCommGrp.{u} := by
  unfold unitsAddCommGrp; infer_instance

/-- The functor sending a commutative ring to its group of units, written additively and lifted
to a larger universe: `CommRingCat.unitsAddCommGrp` followed by `AddCommGrpCat.uliftFunctor`. -/
noncomputable abbrev unitsAddCommGrpULift : CommRingCat.{u} ⥤ AddCommGrpCat.{max u v} :=
  unitsAddCommGrp ⋙ AddCommGrpCat.uliftFunctor.{v, u}

end CommRingCat
