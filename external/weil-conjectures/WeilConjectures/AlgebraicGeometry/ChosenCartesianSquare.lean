/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square

/-!
# Cartesian squares with a chosen pullback identification

Source: blueprint, chap-Cohomology-of-torsion-sheaves-on-curves, sk-prop-cd.

The inverse-image comparison is the existing `Etale.squareUpperStarIso` applied to
`ChosenCartesianSquare.toCommSq`. Its identity and pasting coherence are supplied by
`Etale.squareUpperStarIso_id`, `Etale.squareUpperStarIso_paste_horiz_hom`, and
`Etale.squareUpperStarIso_paste_vert_hom`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A Cartesian square of schemes with its chosen identification with the fibre product.
The two projection equations say that the identification is one of squares, not merely
of schemes. The inherited commutativity gives the canonical inverse-image comparison
`Etale.squareUpperStarIso A sq.toCommSq`, with the identity and pasting compatibility of
that construction. Source: blueprint, chap-Cohomology-of-torsion-sheaves-on-curves, sk-prop-cd,
node definition-underived-base-change-map . -/
structure ChosenCartesianSquare {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    extends CommSq g' f' f g where
  /-- The specified Cartesian identification. -/
  isoPullback : X' ≅ pullback f g
  /-- The identification respects the first projection. -/
  hom_fst : isoPullback.hom ≫ pullback.fst f g = g'
  /-- The identification respects the second projection. -/
  hom_snd : isoPullback.hom ≫ pullback.snd f g = f'

end AlgebraicGeometry
