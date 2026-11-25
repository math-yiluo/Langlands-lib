/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.EtaleFieldGsets
import WeilConjectures.AlgebraicGeometry.Galois.GaloisStalkActionFunctor
import WeilConjectures.AlgebraicGeometry.Galois.GaloisStalkActionFullyFaithful
import WeilConjectures.AlgebraicGeometry.Galois.GaloisStalkActionEssSurj

/-!
# Canonical set-valued stalk equivalence over an algebraically closed extension

Source: Stacks Project, Tags 03QT and 03QW.
-/

@[expose] public section

attribute [instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

-- Keep the quantified proof-binder names in the existing statement.
end AlgebraicGeometry.Scheme
