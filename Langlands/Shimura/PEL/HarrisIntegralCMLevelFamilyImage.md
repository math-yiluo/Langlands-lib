# The normalized class image of one actual integral Harris family

This internal construction works with the actual universe-zero Harris CM
arithmetic data and a fixed polarized abelian scheme `B` over `S`, with its
supplied dual witness, polarization and prescribed relative dimension.
The named tensor, Picard, duality, polarization, Weil, adelic and torsion
prerequisites remain explicit.

`HarrisIntegralCMTestCategory` is the full category of schemes over `S` whose
composite structure map to the CM field satisfies the existing
`AdmissibleCMBase` conditions. Its functor to the existing admissible CM base
category retains the actual composite structure map. In particular each test
is connected, locally Noetherian and quasi-separated, with invertible positive
orders, finite etale roots of unity, Lie naturality, ordered-pair additivity and
existence of constrained dual data.

`HarrisIntegralCMLevelFamilyCondition` singles out compatible normalized CM
class families obtained from a single integral action on the direct pullback
of this fixed `B`. That action satisfies the full-order Rosati equations and
the unchanged normalized determinant. At every actual geometric point, an
actual monodromy-fixed original Harris level orbit on that same direct family
must produce the specified compatible class family. The integral action is
uniform across the points; a representative orbit need not be fixed as a frame.

`harrisIntegralCMLevelFamilyCondition_of_orbit` proves that one actual orbit at
one geometric point supplies this condition. It transports that orbit by the
actual raw point comparison, and uses the previously proved point independence
of the integral-family class map. The same integral action works at all points.
Every original Harris transporter preserves the condition by naturality of
that map, keeping the action and changing the orbit.

`harrisIntegralCMLevelFamilyCondition_pullback` proves preservation under every
morphism in this test category. The new action is literally
`(relativeEndRestrict B f.hom).comp a`; its joint condition follows from the
proved restriction theorem. For each target geometric point, the source
witness is evaluated at the pushed point and its orbit is restricted by the
actual raw restriction. The proved compatible-family base-change square,
specialized to the existing unpointed presheaf's constrained dual choices,
identifies its class family with the original normalized pullback.

`harrisIntegralCMLevelFamilyImageTower` takes the corresponding subtype of the
unchanged compatible-family tower. `harrisIntegralCMLevelFamilyImagePullback`
restricts the original pullback to this subtype.
`harrisIntegralCMLevelFamilyImagePresheaf` inherits identity, composition and
level naturality by subtype extensionality from the existing normalized CM
presheaf. Its inclusion is natural for all original base morphisms and Harris
level transporters.

The provenance is internal: the new image condition uses actual integral
actions and raw level orbits, and its stability follows from the previously
proved actual point and base comparisons. This is the image of a fixed
polarized family, distinct from the existing image allowing arbitrary integral
representatives. It asserts no surjectivity onto all normalized classes, no
representability of this image, and no ordinary moduli existence, smoothness,
division projectivity or output admissibility. Identity and composition of
raw orbit restriction before passing to normalized classes remain separate.
