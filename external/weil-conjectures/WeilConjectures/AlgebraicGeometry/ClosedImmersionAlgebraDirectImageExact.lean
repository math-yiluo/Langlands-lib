/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ClosedImmersionAlgebraDirectImagePreservesEpimorphisms
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Exact direct image over a closed immersion's algebra

Source: Stacks Tags 01AX, 00AE and 0AVW, closed-embedding stalk calculation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Direct image into the direct-image algebra of a closed immersion preserves
finite colimits; its left exactness follows separately from the pullback adjunction.
This concerns all module sheaves, independently of any rank decomposition or
choice of complex.

Source: Stacks Tag 01AX (exact direct image for a closed subset),
Tag 00AE (stalks), and Tag 0AVW (direct-image algebra); reconstruction proof step 1.
(blueprint: lem-sc-closed-immersion-algebra-direct-image-exact)

Proof: At a point in the image of the closed embedding, inverse-image opens
are cofinal among neighborhoods of its unique preimage. The stalk of direct
image is therefore the source stalk, with its unchanged ring action, since
the ring map of toDirectImageAlgebraSpace is the identity. At a point outside
the image, its open complement has empty preimage. The direct-image stalk
is the zero module. Exactness of module sheaves is detected on stalks, so
this functor preserves short exact sequences. An additive exact functor
between abelian categories preserves finite limits and finite colimits.
The empty source is covered by the zero-stalk case. -/
theorem closedImmersion_algebraDirectImage_preservesFiniteColimits
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] :
    PreservesFiniteColimits
      (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i))  := by
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)
  let : F.PreservesHomology :=
    closedImmersion_algebraDirectImage_preservesHomology i
  exact Functor.preservesFiniteColimits_of_preservesHomology F

end AlgebraicGeometry
