/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.RepresentationTheory.Invariants
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.FieldTheory.KrullTopology
import WeilConjectures.FieldTheory.GaloisAutomorphismExtension

/-!
# Sections over a field as geometric stalk invariants

Source: Stacks Project, Tags 03QW and 04JQ, Lemma global-sections-point.
(blueprint: lem-exc-field-module-sections-invariants).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Algebra.Etale.of_finite_of_isSeparable

end AlgebraicGeometry.Scheme
