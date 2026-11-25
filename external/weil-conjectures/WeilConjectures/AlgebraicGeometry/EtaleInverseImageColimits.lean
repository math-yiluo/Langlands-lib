/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Colimits and inverse image of abelian étale sheaves

Source: Stacks Project, Categories, Lemma 0038(1), applied to the inverse-image
adjunction of Étale Cohomology, Definition 03Q0; Étale Cohomology, proof of Lemma 0A4B.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Inverse image of abelian sheaves on small étale sites preserves every small colimit.
Source: Stacks Project, Lemma 0038(1) and the proof of Lemma 0A4B.

First, `upperStarLowerStarAdjunction AddCommGrpCat f` identifies inverse image with the
left adjoint of direct image (`def-weil-pbc-inverse-image`, Definition 03Q0).
Second, apply `situation-conventions` (Lemma 0038(1)) to this
adjunction and any diagram F. The image of its colimit cocone is a colimit cocone.
The canonical map from the chosen colimit of the image diagram to the image of the
chosen colimit is induced by the images of the coprojections
(`def-weil-pbc-category-colimit`). The two colimit universal properties give its
inverse: the composites agree with the identities on every coprojection and hence
are identities by uniqueness. Thus the canonical map is an isomorphism. -/
theorem inverseImage_preservesColimits {U V : Scheme.{u}} (f : U ⟶ V) :
    PreservesColimitsOfSize.{w, w} (upperStar AddCommGrpCat.{u + 1} f) := by
  exact (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).leftAdjoint_preservesColimits

end AlgebraicGeometry.Etale
