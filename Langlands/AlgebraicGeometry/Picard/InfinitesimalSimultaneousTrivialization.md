# Simultaneous affine trivializations in infinitesimal squares

This internal construction supplies actual affine neighborhoods on which both
bundles in an infinitesimal square become trivial. Consider a commuting square
of schemes `Y₀ → Y₁`, `Y₀ → Y₂`, `Y₁ → Y`, `Y₂ → Y`. Suppose the map `Y₁ → Y`
and the overlap map `Y₀ → Y₂` are surjective closed immersions, and `Y₂ → Y` is
affine. Let `L₁`, `L₂` be line bundles on `Y₁`, `Y₂`, with a specified
isomorphism of their actual pullbacks to `Y₀`.

For a point `x` of `Y` and any open neighborhood `V`,
`simultaneousAffineNeighborhood` chooses an affine open `U` containing `x`,
contained in `V`, and actual isomorphisms from the pullbacks of `L₁`, `L₂` to
the structure modules on the inverse images of `U`. The result is packaged as
`SimultaneousAffineNeighborhood`.

The surjective closed immersion `Y₁ → Y` is a homeomorphism of underlying
spaces, constructed as `closedImmersionHomeomorph`. Transport a trivializing
open of `L₁` around the unique point over `x` to `Y`, intersect with `V`, and
choose an affine neighborhood inside that intersection using the affine-open
basis of a scheme. The inverse image of this neighborhood is contained in the
chosen trivializing open, giving the first actual module isomorphism.

The inverse image of `U` in `Y₂` is affine. Restrict the closed immersion
`Y₀ → Y₂` to this affine open; it is still surjective and a closed immersion,
so its actual global ring map is surjective and its domain is affine. The
specified overlap isomorphism and the first trivialization, transported through
the ordinary pullback-composition comparisons and the square equation, trivialize
the pullback of `L₂` to this domain. The published
`affinePullbackTrivialization` lifts that frame and reflects its generation open,
producing the second trivialization on the actual inverse image in `Y₂`.

`relativeMap_isClosedImmersion` proves that a surjective algebra map induces a
closed immersion on the actual relative spaces. For a nilpotent kernel,
`relativeMapHomeomorph` constructs the corresponding homeomorphism of underlying
spaces by base-changing the proved surjective closed immersion of spectra.
No field, properness or finiteness hypothesis enters these constructions.

For an actual algebra pullback square `R → A`, `R → B`, `A → C`, `B → C`
with `B → C` surjective and its kernel nilpotent,
`affineSquareNeighborhood` specializes the construction to the square on
`X × Spec A`, `X × Spec B`, `X × Spec C`, `X × Spec R` formed by
`relativeSpace f` and the actual `affineBaseMap` arrows. The published ring
pullback lemmas make `R → A` a nilpotent surjection. Both corresponding
relative arrows are therefore surjective closed immersions; the other
relative arrow is affine by base change. The isomorphisms returned are the
ordinary module pullbacks to the actual inverse-image opens. Any open `V` is
allowed, so the same statement refines neighborhoods within overlaps.

The construction is derived from the published actual line-bundle pullback,
affine nilpotent frame-lifting and relative-space interfaces, and Mathlib's
closed-immersion base-change and affine-open-basis results. It does not assert
effectivity or full faithfulness of the global Picard gluing comparison.
