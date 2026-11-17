# Local based coordinate alignment of actual comparisons

For two affine pinned models `M`, `N`, any scheme `T`, base maps `f`, `g`,
a supplied comparison `e`, and a supplied coordinate-torus isomorphism `τ`,
assume their exact inclusion square and `PreservesBorel e`.
`basedAlignmentNeighbourhood e τ hτ hb x` constructs, for every point `x` of
`T`, an open neighbourhood containing `x` and a `BasedCoordinateIso` there.
Its group and torus maps are exactly `pullComparison e W.ι` and
`splitTorus.pullIso τ W.ι`. Its root equivalence preserves simple supports,
both coordinate pairings are the standard dot products, and its character
formula holds for every exponent on every relative test scheme over `W`.
No connectedness, affineness, quasi-compactness, or nonemptiness assumption on
`T` is used. The assertion at a point has no instances when `T` is empty.

The structure `BasedAlignmentNeighbourhood` records this neighbourhood, the
based data, and the two equalities of actual isomorphisms.
`BasedAlignmentNeighbourhood.preservesCocharacter` deduces transport of the
exact canonical positive-coroot cocharacter on the selected neighbourhood
from the existing `BasedCoordinateIso.cocharacter_comp` theorem.

This is an internal deduction from `AffinePinnedFieldAlignment`,
`AffinePinnedComparisonPullback` and `Torus.LocalExponentTransport`:

1. `torusSquare_pull` proves that the supplied actual torus square persists
   under normalized pullback, retaining all base-change comparison maps.
2. `exists_fieldCoordinateData` equips any field mapped to the two coefficient
   spectra with the induced algebra structures. Equality of the induced and
   supplied spectrum maps transports the comparison to the algebra-map
   endpoints. Applying `fieldBasedCoordinateIso` and extracting its root
   equivalence, simple-support law, pairings and entire-character formula
   removes those auxiliary endpoint equalities from the conclusion.
3. At `x`, use the actual map from its residue-field spectrum to `T` and pull
   back both `e` and the specified `τ`. The Borel square persists by
   `PreservesBorel.pull`. The preceding field lemma gives one full root
   equivalence and the formula for this exact pulled-back torus map.
4. `splitTorus.exists_open_character_pullHom` spreads that entire weight map
   to an open neighbourhood by local constancy. Its formula is quantified
   over all relative tests, so it is directly the character clause of
   `BasedCoordinateIso`. The other clauses are unchanged field-coordinate
   data and the normalized inclusion square. Classical choice packages the
   existence theorem `exists_open_basedCoordinateIso` as the displayed
   construction.

The hypotheses already include the Borel and torus squares. This module does
not construct the initial inner correction or align the chosen pinning vectors,
and does not prove `RelativePinnedComparisonExistenceStatement` by itself.
