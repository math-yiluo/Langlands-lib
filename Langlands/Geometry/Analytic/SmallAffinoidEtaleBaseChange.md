# Actual finite small affinoid étale base-change squares

This internal construction combines `SmallAffinoidPointwiseSquare`,
`AffinoidPointwiseBaseChange`, and `SmallAffinoidEtaleRealization`. It assumes
the finite Banach pushout and finite tensor comparison propositions.
The original bounded map `f : A → B` is finite Banach and étale at every ordinary
spectrum point; `g : A → C` is an arbitrary bounded map. The three original
spectra are small in the supplied space universe, independent of the field
universe.

`finitePushout` is the existing small saturated realization of the actual
closed-quotient affinoid pushout. Finite Banach base change makes its right
leg finite and therefore makes its spectrum small in the universe of the
spectrum of `C`. The two projections retain the entire original bounded
pushout maps. Their commuting equation is the bounded pushout equation
transported by the small-spectrum functor.

The finite tensor comparison theorem transfers pointwise étaleness to the
right leg at every spectrum point. The small affinoid realization theorem
then proves that the second projection is canonically strong étale and is
étale for the actual localized analytic category. Compatible prescribed
ordinary points lift to the original pushout spectrum and hence to this
small saturated space. This gives `exists_finite_etale_pointwiseSquare`
with an equality of full strong morphisms and localized étaleness of its
second projection.

The finite base-change propositions remain explicit premises. This module
does not establish local finite models for arbitrary analytic étale maps,
or the unrestricted site-level lifting statement.
