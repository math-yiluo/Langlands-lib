/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.EtaleFieldGsets
import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts
import WeilConjectures.FieldTheory.GaloisAutomorphismExtension
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Finite actions in the essential image of the Galois stalk functor

Source: Stacks Project, Tags 03QT and 03QR.
-/

@[expose] public section

attribute [instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
