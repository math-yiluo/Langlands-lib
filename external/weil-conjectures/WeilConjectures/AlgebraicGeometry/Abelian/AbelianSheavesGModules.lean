/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
public import WeilConjectures.AlgebraicGeometry.EtaleFieldGsets
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
import WeilConjectures.AlgebraicGeometry.Abelian.AbelianSheavesGModulesData
import WeilConjectures.AlgebraicGeometry.Abelian.AbelianSheavesGModulesAction

/-!
# Abelian etale sheaves on a field and discrete Galois modules

Source: Stacks Project, Etale Cohomology, Tag 04JQ,
`lemma-equivalence-abelian-sheaves-point`, deduced from Tag 03QT
(blueprint: lem-exc-abelian-sheaves-gmodules).
-/

@[expose] public section

attribute [instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
