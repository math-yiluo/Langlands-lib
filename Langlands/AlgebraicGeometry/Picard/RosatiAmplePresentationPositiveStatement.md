# Integral Rosati positivity with a ground-field ample presentation

`Langlands.AbelianScheme.Rosati.AmplePresentationIntegralPositiveStatement` is an internal proof obligation used to separate the numerical argument from descent along extensions of fields. It is not a proof of positivity.

For every algebraically closed characteristic-zero field in universe `u`, it uses the existing actual abelian scheme, chosen dual data, dual-additivity witness, map to that dual, and rational-inverse instance. If the underlying map has an actual `HasAmpleMumfordPresentation` over that same field, it asks for `IntegralDiagonalPositive`: strict positivity of the fixed geometric Rosati trace form on the rationalizations of nonzero integral endomorphisms.

There is no positive-dimension condition, so a proof must include dimension zero. The target uses the existing `traceForm` and `geometricEndomorphismTrace`, rather than an independently supplied pairing. It adds no relative-polarization hypothesis: the explicit ample presentation is the geometric input in this intermediate obligation. A proof of this predicate alone does not give the final `PositivityStatement`, which also requires descent from presentations after extensions of fields, rational denominator clearing, and symmetry.

The provenance is an internal decomposition of the published `IntegralDiagonalPositive` in `RosatiPositivityReduction` obligation using the published `HasAmpleMumfordPresentation` predicate. No new literature claim is made.
