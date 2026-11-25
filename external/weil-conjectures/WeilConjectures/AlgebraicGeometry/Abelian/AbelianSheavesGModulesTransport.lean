/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.AlgebraicGeometry.EtaleFieldGsets
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import WeilConjectures.CategoryTheory.DiscreteContinuousRepCommGrp
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Transport of abelian group objects across a set-valued sheaf equivalence

Source: Stacks Project, Tag 04JQ, proof of lemma-equivalence-abelian-sheaves-point.
(blueprint: lem-exc-abelian-sheaves-gmodules-transport)
-/

@[expose] public section

attribute [instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
