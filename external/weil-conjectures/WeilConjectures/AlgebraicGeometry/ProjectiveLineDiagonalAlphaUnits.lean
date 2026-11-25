/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalMaps

/-! # The cached diagonal source unit as the supported-unit composite

Source: blueprint lemma-class-diagonal-projective-line, the canonical source identification.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
set_option linter.auxLemma false in
attribute [local instance 100000] ordinaryFiniteClass._proof_1 ordinaryFiniteClass._proof_2
  ordinaryFiniteClass._proof_3
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors

/-- The cached pair of constant single-object units is the original supported-unit pair.
Source: blueprint lemma-class-diagonal-projective-line, alpha and unit pasting.
(auxiliary; not a blueprint node)

Proof: expand the cached pair and the two supported units. Both are the same
composite of derived single-object units, using the canonical constant-sheaf
pullback comparison at the free rank-one coefficient module. -/
theorem projectiveLineDiagonalAlpha_units (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) (a : Bool) :
    projectiveLineDiagonalAlpha A S a =
      supportedDerivedUnit A (projectiveLineDiagonalProjection S a) ≫
        (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
          (supportedDerivedUnit A (pullback.diagonal (ProjectiveLine S ↘ S))) := by
  unfold projectiveLineDiagonalAlpha constantSingleSectionUnits supportedDerivedUnit
  rfl

end AlgebraicGeometry.Etale
