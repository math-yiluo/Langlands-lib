# Actual spherical spectra of the rank-one constant presentation

This internal construction attaches actual unramified data to the constant
tensor presentation and produces a `CuspidalSpectralPresentation` of
`ConstantFunctions.rankOneCuspidal` in every independent factor universe.
It supports the rank-one clause of `RelativeIsometryOperationStatement`.
It does not yet prove a relative Weil association.

The proof first computes the action of a normalized double coset whose
representative normalizes the compact open subgroup. Its test function is the
left translate of the corner unit, and `integratedAction_leftTranslate` together
with `heckeAction_normalizedIndicator_of_fixed` identifies its action with the
original group action. Thus no additional Haar mass is assumed.

For rank one, each standard diagonal is central. A trivial group action
therefore makes both standard Hecke operators the identity. The singleton
spectrum `{1}` has normalized scalars one for both indices, Euler polynomial
`1 - X`, and every power trace equal to one.

Each local component of the actual constant tensor presentation is equivalent
to its specified trivial lifted scalar factor. This proves triviality of its
action. The actual nonzero integral-fixed reference vector supplies nonzero
spherical fixed space. These facts prove the spectrum equations on the whole
fixed space and give `rankOneUnramifiedData`. Together with the whole actual
finite slice, they construct `rankOneSpectralPresentation`.

All ingredients are derived from the constructed restricted tensor presentation
and actual integrated Hecke action. No new external literature assertion is
used.
