# An affine-open criterion across a principal divisor

This is an internal helper for the smooth DVR identity-component proof. Let `X`
be affine, let `D(f)` be a dense principal open, and let `U` be open. Assume every
point of `X` has an irreducible open neighborhood, that `U` restricts to a closed
subset of `D(f)`, and that `U \ D(f)` is closed in `X`. Then `U` is affine.

The proof first observes that the closure of every open set is open in a space
with irreducible open neighborhoods. Put `C = closure (U ∩ D(f))`. Density gives
`U ⊆ C`, and relative closedness gives `C ∩ D(f) ⊆ U`. The inclusion of `U` is
affine locally on `X`: near a point of `U` it is the whole chosen affine chart;
outside `C` it is empty; and at a point of `C \ U`, closedness of `U \ D(f)`
provides a chart on which `U` equals `D(f)`. Each inverse image is affine, so
the inclusion is affine. As `X` is affine, this proves affineness of `U`.

This argument is derived here from Mathlib's irreducibility, closure, principal
open and target-local affineness lemmas. It does not use an affineness theorem
for group schemes, or assume that `f` globally generates any selected component
of its zero locus. Its application to DVR group schemes still needs regularity,
density of the generic fibre, and the actual fibre-image comparisons.
