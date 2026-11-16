# Composition for the actual analytic étale predicate

Author: Worker 208.

This derived unit proves composition for the existing localized `etale`
predicate used by the actual analytic `EtaleSite`. It retains independent
field and space universes `u, v`, arbitrary complete ultrametric normed
coefficient fields, and non-Hausdorff spaces. It does not yet prove the
unrestricted pointwise-lifting target or unconditional general étale
right cancellation.

`localizedFractionEtale_of_isIso` uses the full quasi-isomorphism fraction
constructed for every localized isomorphism. Its numerator is strongly
étale by the existing quasi-isomorphism consequence, so the isomorphism
has the intrinsic fraction property. The latter property was already
proved multiplicative; therefore precomposition and postcomposition with
isomorphisms give a `RespectsIso` instance. These assertions apply to the
intrinsic localization with independent original chart-index universe
`w` as well.

For the actual site's universe convention, `localizedFractionEtale_eq_etale`
combines this invariance with the preceding exact equality
`etale = localizedFractionEtale.isoClosure`. The closure is now the
property itself. Consequently `etale_comp` and its
`IsStableUnderComposition` instance transfer intrinsic fraction
multiplicativity to the original site's predicate, without modifying it.

`etale_localizationFunctor_map_iff_strongEtale` gives the exact canonical
strong-map test for every mapped actual arrow. On maps between
constructed saturations,
`etale_localizationFunctor_map_ofSaturation_iff` identifies it with the
original `IsEtaleAllPieces` condition. Thus arbitrary localized
isomorphisms in the site's definition no longer obstruct recognition of
the supplied strong representative.

Finally, `etale_hasOfPostcompProperty_of_strong` transports a specified
right-cancellation property for the canonical `strongEtale` class to
right cancellation for the actual localized `etale` class. This theorem
retains that strong geometric property as an explicit premise. For
fractions `φ, ψ`, étaleness of the second arrow gives a strongly étale
second numerator. Étaleness of the composite gives the condition on the
Ore lift followed by that numerator. The assumed strong cancellation
makes the lift strongly étale. Postcompose by the second denominator and
use the exact Ore square; source-denominator invariance then gives
étaleness of the first numerator. The class equality returns exactly the
original localized conclusion. No unconditional general cancellation is
asserted by this transport theorem.

The complete implementation uses the actual fraction calculus,
quasi-isomorphism reflection, previously proved all-pieces transport and
the existing site predicate. It neither assumes a base-change statement
nor adds compactness, separation, supplied pullback or equal-field/space
universe hypotheses. All provenance is internal derived infrastructure.
