# Affine cocycle vanishing on arbitrary single fppf covers

This internal helper extends the published affine-cover vanishing theorems to
flat, surjective, locally finitely presented single covers whose total space
need not be affine or quasi-compact. All schemes have arbitrary universe `u`.

`CocyclesVanish.isTrivial_on_affine` extracts direct vanishing for a group `H`
over `Spec R` from the published `CocyclesVanish H`. It applies that predicate
to the identity base change, restricts the cocycle along the identity-on-total-
space comparison, and reflects the resulting base-change triviality and then
refinement triviality. `isTrivial_on_fppf` applies the affine fppf refinement
reduction. `isTrivial_on_fppf_baseChange` applies the same reduction after any
affine test `T` over `Spec R`.

`Cocycle.isTrivial_fppf_of_isVectorGroupOfDimension` and
`isTrivial_fppf_of_isFiniteVectorGroupRetract` apply the affine fppf reduction
to the published coordinatewise additive-cocycle vanishing and its actual
retraction corollary. Their base `B` is any scheme and their test `T` is affine.
The dimension may be zero; a retraction is supplied by actual group-scheme
homomorphisms.

`isTrivial_fppf_of_hasAffineVectorSeries` combines
`HasAffineVectorSeries.cocyclesVanish` with the direct fppf extension. The ring
`R` is arbitrary; the group has an affine structure map and a supplied finite
series with finite-dimensional vector-group quotients. The definition
`affineVectorSeriesFppfCochain` chooses a trivializing morphism on the original
cover, and its specification states the coboundary identity on every scheme
test. `isTrivial_fppf_of_hasSplitSeries` uses the published conversion of a
split series into an affine vector series.

The provenance is internal: all vanishing on affine covers is imported from
`AffineVectorSeries` and `SplitUnipotentTorsor.VectorRetract`; the extension
uses `CocycleAffineRefinement`, and removal of the identity base change uses
`CocycleRestriction`. No field hypothesis is added. This module does not
construct a series from a geometric unipotence predicate, or a vector-group
retraction from a vector-bundle predicate, and it does not prove the reductive
quasi-split inner-form statement.
