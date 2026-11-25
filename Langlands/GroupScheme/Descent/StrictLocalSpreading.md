# Spreading group isomorphisms from a strict-local affine limit

`Langlands.GroupScheme.Descent.StrictLocalSpreading.isomorphismNeighborhood`
chooses a level and an actual isomorphism of two affine locally finitely
presented group schemes over that level from an isomorphism after pullback
to a supplied `StrictLocalEtaleLimit`. The original base is affine. Every level
is affine and etale over the base, by the data package.

The construction applies
`Langlands.GroupScheme.Descent.AffineLimit.isomorphismModel` to the supplied
limiting cone. `exists_etale_neighbourhood_iso` retains the fact that the
selected level meets the prescribed point: the projection of the local ring's
closed point lies above it. The chosen group isomorphism is not required to
recover the specified limit isomorphism.

This is an internal application of generic affine-limit isomorphism descent
and the actual cone compatibility equations. It does not construct a strict
henselization or assert existence of `StrictLocalEtaleLimit`. It supplies a
conditional spreading interface, not the full multiplicative-type theorem.
