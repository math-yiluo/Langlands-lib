# Affine pullback of ample Mumford presentations

This internal CM polarization helper works with actual schemes, line bundles,
and dual parameter schemes. The scheme morphism underlying `g : Y ⟶ X` is
affine in the presentation-transport theorem. No field, reducedness, or
noetherian hypothesis is used.

`affinePullbackAmple` proves that an affine morphism pulls an ample line bundle
back to an ample line bundle. It reuses `LineBundle.pullbackPowSection` and
`LineBundle.sectionOpen_pullbackPowSection`: every pulled-back positive-power
section generates on exactly the inverse image of its original generation
open. The original affine opens therefore have affine inverse images.
An affine morphism is quasi-compact, and
`QuasiCompact.compactSpace_of_compactSpace` gives compactness of the source.
This is the arbitrary-affine version of the published field-base-change proof;
it does not duplicate the construction of pulled-back sections.

`dualPullbackMumfordPoincareIso` constructs an actual ordinary line-bundle
isomorphism on `Y ×_T Y`. Its source is the Poincare family of `Y` pulled back
by the composite `g` then `fX : X.X ⟶ dualScheme X hX` then the actual
contravariant `dualSchemeMap` of `g`. Its target is the Poincare family of `X`
pulled back by `fX` and then by the map `g × g` of self-products. The defining
`dualSchemeMapPullbackIso` supplies the family isomorphism; actual line-bundle
pullback composition supplies the rest. Equality of the two composite maps
of fibre products is proved by their first and second projections.
Thus Poincare compatibility is constructed, with no compatibility hypothesis.

`hasAmpleMumfordPresentation_dualPullback` transports an existing
`HasAmpleMumfordPresentation` along any affine `g`. It retains the displayed
pullback-tensor and Mumford Picard-zero prerequisites. Its presentation uses
the actual bundle `g^*L`, the same base bundle `B`, the published pulled-back
unit evaluation, and `g^*M` with the published pulled-back inverse evaluation.
Ampleness follows from `affinePullbackAmple`. The classifier equality follows
from `dualPullbackMumfordPoincareIso`, the existing classifier isomorphism,
and `mumfordBundlePullbackIso`; `nonempty_iso_of_forget_iso` restores the
rigidification along the retracting section.

The provenance is internal: these constructions combine published pullback,
Poincare classification, and Mumford-family identities. This gives an actual
ample presentation on an affine pullback. It does not assert that a rational
isomorphism is an isogeny, that its dual is an isogeny, or that the relative
`IsPolarization` predicate or the CM representability proposition holds.
