# Same-universe pullback existence along localized etale maps

This internal construction proves existence of pullbacks for every cospan
with an etale first leg in the actual existing localized analytic
category. The coefficient-field universe remains independent of the
unchanged common space and atlas-index universe. There is no supplied
size, Hausdorff, finite-cover, tensor-base-change or lifting premise.

First represent the three arbitrary localized objects by saturated
presentations. Represent each of the two arrows by an actual right
fraction with a full quasi-isomorphism denominator. The first numerator
is canonically strong etale: its localized map is the original etale map
precomposed with the invertible denominator, and the exact
localized/strong etale comparison reflects that property.

The recognized-cospan construction gives a full limiting cone over these
two strong numerators. Its explicit finite Banach pushout input is
discharged by the unchanged `AffinoidPushout.finiteBanachPushout` proof
of the unrestricted published finite Banach base-change statement.
Thus actual quotient smallness, the complete geometric cone lifts,
their bounded pullbacks and the full localized universal property are
all established by the imported constructions.

The denominator maps are actual isomorphisms in the localization.
Transport of the complete limiting square along them gives a pullback
over the original two arbitrary localized arrows. The cone's legs are
the numerator-square projections followed by their respective
denominators. `localizedEtalePullback` chooses such a cone together with
its `IsLimit`.

This is the existence part of `LocalizedEtalePullbackStatement`. It does not assert that
the base-changed projection is etale; that geometric base-change part
is needed for the full `LocalizedEtalePullbackStatement`, which is proved
in `LocalizedEtalePullbackProof`. No assumption of that target or of
its etale conclusion occurs.

The proof is internally derived from the actual original-domain gluing,
full bounded-map separation, recognition comparisons and fraction
calculus. The finite Banach base-change proof is reused unchanged. The
recognition and categorical reduction constructions come from the Library
modules imported through `RecognizedLocalizedPullbacks`; the
arbitrary-fraction transport here follows the existence part of that
reduction. No external theorem
is transcribed.
