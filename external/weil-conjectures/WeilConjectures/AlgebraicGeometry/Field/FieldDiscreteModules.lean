/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RepresentationTheory.Invariants
public import WeilConjectures.AlgebraicGeometry.Abelian.AbelianSheavesGModules
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
import WeilConjectures.AlgebraicGeometry.SmoothPurity.SepClosedEtalePointComparison
import WeilConjectures.CategoryTheory.ScalarObject.ScalarStalkTransport
import WeilConjectures.AlgebraicGeometry.Field.FieldModuleSectionsInvariants
import WeilConjectures.FieldTheory.GaloisAutomorphismExtension

/-!
# Etale modules on a field and discrete Galois modules

Source: blueprint `sec-curve-estimates/sk-prop-h2/lem-exc-field-discrete-modules.md`,
node `lem-exc-field-discrete-modules` (blueprint: lem-exc-field-discrete-modules).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
