# Small actual affinoid squares with prescribed ordinary points

This internal construction combines the actual closed-quotient affinoid
pushout with the small singleton spectrum presentations. All three given
spectra are supplied as small in an independent universe. When the pushout
spectrum is also small, `pushout` is its small saturated realization.
The projections `pushoutFst` and `pushoutSnd` retain the original left and
right bounded pushout maps. These definitions supply the object and maps
used by the pointwise square construction; no categorical universal
property is claimed for them here. The original bounded pushout equation gives an
equation of complete saturated morphisms, by the composition theorem for
the small spectrum construction. In particular, equality of morphisms is
obtained from the bounded algebra equation.

For compatible ordinary points, the proof transports them back to their
original spectra, applies the existing `AffinoidPushout.exists_point`, and
transports the resulting point to the small realization. The two prescribed
point equations follow from the spectrum equations of the original maps.
The proof makes no assertion that such a point is unique.

The last theorem assumes `FiniteBanachPushoutStatement K` and a finite Banach
left leg. The statement's smallness consequence supplies a small pushout
spectrum in the same independently chosen universe. The theorem then packages
the object, its two complete morphisms, their commuting equation, and the
lifted point. This is a conditional affine prerequisite: neither étaleness
of its projections nor unrestricted lifting in the analytic étale site is
asserted. Its provenance is the already constructed affinoid pushout,
ordinary-point amalgamation, small spectrum realization, and finite-fibre
smallness argument.
