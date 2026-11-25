/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.SuccessiveQuotientFlatTensorSequence
import Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.AlgebraicGeometry.Adic.AdicReductionTriangle
/-! # Self-reduction along a regular quotient of coefficient sheaves -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private local instance restriction_faithful
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) : (pbcRestrict φ).Faithful where
  map_injective := by
    intro M N f g h
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) h

end AlgebraicGeometry.Scheme
