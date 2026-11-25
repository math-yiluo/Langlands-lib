/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-!
# `CommGrpCat.toAddCommGrp` is an equivalence

Mathlib builds the equivalence `commGroupAddCommGroupEquivalence` between commutative groups
and additive commutative groups, but does not register its functor
`CommGrpCat.toAddCommGrp` as an equivalence. Instance search therefore does not know that
`CommGrpCat.toAddCommGrp` is a right adjoint, and so does not know that it preserves limits.
This file supplies the missing instance.
-/

@[expose] public section

universe u

open CategoryTheory

noncomputable instance : CommGrpCat.toAddCommGrp.{u}.IsEquivalence :=
  inferInstanceAs commGroupAddCommGroupEquivalence.functor.IsEquivalence
