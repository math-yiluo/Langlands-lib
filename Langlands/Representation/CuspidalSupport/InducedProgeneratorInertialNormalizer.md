# Induced progenerators when a Levi normalizer fixes the inertial class

Renard (2026), VI.10.1 Lemma, printed p. 207 and PDF p. 213, compares normalized induction of a common Levi progenerator from opposite parabolics in the maximal-Levi case. The fixed-inertia case of that proof uses a normalizing element outside the Levi.

`inducedProgeneratorIso_of_inertialNormalizer` applies the all-test range comparison to show that the normalizing element carries the first parabolic to the second. The intertwining equation for the irreducible representation is evaluated on the inverse point map of the Levi automorphism, giving an isomorphism from the inverse pullback to an unramified twist. That inverse point map preserves the common norm kernel, so `nonempty_pullback_rationalNormKernelSummandInduction_iso` identifies the pulled-back progenerator with the original one. Conjugation of normalized induction followed by induction of this isomorphism gives the comparison.
