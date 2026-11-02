# Finite affine quotient charts for the tuple cross-cover action

This module specializes the compact-image quotient-cover construction to the
actual tuple cross-cover action. Its provenance is the symmetric-tuple
filtration in the Stacks Project, Lemma 68.8.6, Tag 07ST, and the construction of
the symmetric tuple charts and their image opens in Lemma 68.8.3, Tag 0BBN.
The registered originals are `stacks-noetherian-approximation-2026-11-01`
(`07ST.txt`) and `stacks-stratification-2026-11-02` (`0BBN.txt`).
The specialization and the affine instances are derived internal scheme
constructions.

Work in arbitrary universe `u`. Let `E` be an étale equivalence relation with
separated source, affine object and arrow schemes, and closed joint endpoint
map. Fix natural numbers `N`, `p`, `q` with `p ≤ q`. Write `L` and `H` for
the tuple tails beginning at `p` and `q`, respectively. The cross scheme is
`P = L.R ×_{L.U} H.U`, using the source of `L` and the higher-tail inclusion.
The published cross-cover action makes `P` an `H`-scheme.

`tupleTailCrossCoverAction_object_isAffine` identifies the object scheme of
the action relation with `P` and uses the established affine cross-scheme
instance. `tupleTailCrossCoverAction_relation_isAffine` applies the general
affineness result for action relations: its arrow scheme is the pullback of
the affine arrow scheme of `H` along the map from the affine scheme `P` to
the affine object scheme of `H`.

For `q < N+1`, `tupleTailCrossCoverAffineQuotientCover` constructs a finite
invariant affine open cover of the action relation on `P`. Each restricted
chart relation has an actual affine scheme quotient, including its
kernel-pair, flatness, local finite presentation, and surjectivity witnesses.
The proof applies `invariantAffineQuotientCoverOfCompactImage` to the lower
target map `P → L.U`. The imported kernel-pair theorem identifies this map's
kernel pair with the action relation. Its image is the compact open
`q`th threshold in `L.U`; the image formula uses `q < N+1` to include the
lowest chart of the higher tail. Pulling back a finite affine cover of this
compact image gives the required cover and its quotient witnesses.

The constructed cover can be supplied to
`InvariantAffineQuotientCover.descend` for a cofiltered cartesian diagram
whose limiting relation is this action relation. This module constructs
neither that diagram nor a glued quotient scheme or a Noetherian first level.
