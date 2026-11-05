# Finite separation and actual affine chamber transport

This helper unit belongs to the proof of the published
`Langlands.Geometry.Building.AffineChamberSimpleTransitivityStatement`.
It proves finite separation, covariance under the existing actual affine action,
and the empty-arrangement case; it does not establish nonempty chamber transport
or triviality of nonempty chamber stabilizers.

The hypotheses and conventions are the existing
`AffineRootSystem.IsAffineRootSystemWithRankZero`, independent universes for
`V` and its real affine torsor `A`, and the existing root and chamber sets.
No reducedness or extra geometric premise is imposed.

## Implemented route

`segmentRoots Ψ x y` is the set of roots in `Ψ` whose endpoint values
have nonpositive product. Over the reals this is the algebraic criterion for the
zero hyperplane to meet the closed segment, including either endpoint. The
definition uses this endpoint criterion directly and requires no topology.

`IsAffineRootSystemWithRankZero.finite_bounded_at` partitions the roots by the
finite derivative set. In each fibre it chooses a reference root. The difference
of two roots in that fibre is constant on the torsor, so a bound at a single point
gives the uniform difference bound required by corrected AR4. The bound may depend
on the derivative. A finite union of these finite subsets proves the result.

`IsAffineRootSystemWithRankZero.finite_segment_roots` bounds the absolute value
of a root at `x` by the absolute change between `x` and `y` whenever the endpoint
values have nonpositive product. That change is its derivative evaluated at
`y -ᵥ x`. The preceding finite-bound lemma therefore proves finiteness, including
roots vanishing at either endpoint.

The imported `image_facet` and `IsChamber.image` from
`IwahoriWeylChamberLemmas` supply the actual facet and chamber transport under
root-preserving affine automorphisms. `IsChamber.image_affineWeylGroup` reuses
that chamber theorem and the existing containment in the root stabilizer.

For the empty arrangement, unfolding the generating set gives the bottom
subgroup, and the sign relation is universal, so every chamber is the whole
torsor. `existsUnique_chamber_transport_empty` uses the identity and bottom
subgroup membership to prove the exact existence-and-uniqueness conclusion.
These arguments in fact hold on any real torsor, without needing the
rank-zero root-system premise.

## Provenance and remaining work

These are internal derived lemmas, proved directly from the published definitions
and AR4. The source motivation is Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Definition 1.3.1 and Remark 1.3.16, with the November 2024
correction to AR4. The exact source IDs, hashes and interpretation of rank zero
are recorded in the unchanged imported statement's Markdown. No external Lean
implementation is adopted. The general finite-separation reflection-arrangement
argument and its application to nonempty affine root systems remain required
before the global simple-transitivity target can be proved.
