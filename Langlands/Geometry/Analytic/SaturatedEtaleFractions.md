# Intrinsic étale numerator conditions on actual right fractions

Author: Worker 208.

This derived internal unit defines `localizedFractionEtale` on the actual
localized category of saturated presentations. It is built from the
canonical strong-map property `strongEtale`. Its equality with the
existing localized `etale` predicate used by `EtaleSite` remains to be
proved; the present composition theorem alone does not establish
composition or right cancellation for that existing predicate.

Work over a complete ultrametric normed field `K : Type u`, with
independent space and original atlas-index universes `v` and `w`.

## Representative independence

`isQuasiIso_of_comp_right` specializes the preceding full
quasi-isomorphism cancellation theorem to actual saturated category
composition. In a common refinement of two right fractions, each
comparison arrow is therefore a quasi-isomorphism: its composite with the
corresponding denominator is the common full quasi-isomorphism.
`strongEtale_numerator_iff_of_commonRefinement` applies source invariance
of `strongEtale` to those two comparison arrows and uses equality of the
entire refined numerators.

For fixed original objects `A, B`, `fractionEtale h` means that an actual
right fraction representing `h : localizationFunctor.obj A ⟶
localizationFunctor.obj B` has a `strongEtale` numerator.
`fractionEtale_localizedRightFraction_iff` proves that every representative
gives exactly the same test, using the published equivalence between
localized fraction equality and common refinement.
`fractionEtale_localizationFunctor_map_iff` applies this to the identity
denominator: the test on an original mapped arrow is exactly its
`strongEtale` condition.

## Composition and denominators

`strongEtale_rightFractionComp` uses the constructed Ore square between
the first numerator and second denominator. Its source comparison is a
quasi-isomorphism, so its composite with the first numerator is strongly
étale. The square equation and target quasi-isomorphism invariance then
show that the Ore lift is strongly étale. Composing it with the second
numerator gives the numerator of the constructed composite fraction.
`fractionEtale_comp` uses the already proved equation interpreting this
Ore composite in the actual localization.

`fractionEtale_id` uses the identity fraction.
`fractionEtale_localizedQuasiIso_inv` represents an inverse denominator by
that denominator and an identity numerator.

## A property on all localized objects

The selected definition `localizedFractionEtale` uses the fixed object
bijection `localizedObjectEquiv`. It transports an arrow from arbitrary
localized objects to the images of their corresponding original objects
using equality morphisms and applies `fractionEtale` there.
`localizedFractionEtale_iff` shows that this reduces to the previous test
on original presented objects. Surjectivity of the object bijection and
`fractionEtale_comp` supply the `IsMultiplicative` instance.
`localizedFractionEtale_map_iff` proves exact agreement with `strongEtale`
on all actual strong maps.

The final results place inverse denominators in this global property and
prove preservation and reflection under source or target composition with
a quasi-isomorphism image. For the reflecting direction, compose with the
inverse denominator and cancel its actual isomorphism identity. These
results allow the other localized endpoint to be arbitrary. They do not
assert preservation under every localized isomorphism.

All arguments use existing actual right fractions, full bounded-map
common refinement, the constructed Ore square and proved strong-map
quasi-isomorphism invariance. No external theorem translation, unproved
geometric premise, separation hypothesis or supplied Ore data is used.
Unchanged prerequisite pairs are included for dependency completeness
while their earlier independently reviewed submissions await integration.
