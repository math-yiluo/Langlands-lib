# Finite pointwise étale maps of small actual affinoid spectra

This internal adapter retains the actual algebras and bounded maps of
`SmallAffinoidSpectrum`. It assumes `FiniteBanachPushoutStatement K` and
`FiniteTensorComparisonStatement K`. The original bounded map must be finite
Banach and étale at every ordinary spectrum point. These hypotheses imply
étaleness of its actual localized small-spectrum map. The unrestricted
pointwise lifting theorem is not established here.

The original singleton presentation has index universe zero, while the
all-pieces predicate in `strongEtale` is tested on the canonical saturation
of the already saturated presentation. `globalChart` retains the singleton
chart in the first saturation; `canonicalGlobalChart` retains it again in the
second. Both charts have global range. Their algebras are propositionally
equal to the original affinoid algebra.

`canonicalMap` is the extension used by the definition of `strongEtale`.
Recovery of the original bounded pullback through both saturation steps
gives `canonicalMap_pullback_global_heq`. Eliminating the algebra equalities
transfers finite Banach finiteness and pointwise étaleness of the original
bounded map to this actual pullback. The global-chart theorem from
`RecognizedPointwiseEtale` then gives étaleness over all pieces, exactly the
canonical strong condition. The existing comparison theorem yields the
localized predicate used by the actual analytic étale site. The field and
space universes remain independent.
