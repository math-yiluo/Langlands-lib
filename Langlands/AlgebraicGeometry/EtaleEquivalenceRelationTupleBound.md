# A uniform bound on distinct related tuples

For an étale equivalence relation `E` whose object and relation schemes are
affine, this module bounds the length of a related tuple with distinct
coordinates. As in the preceding tuple modules, index `n` means `n + 1`
coordinates. The distinct locus also uses the separatedness of `E.s`.

`tupleLengthBound` is the natural number `affineEtalePointBound E.s`. Its
construction uses the étaleness of the source map and depends only on that
affine morphism, independently of the test field or tuple.

`tupleDistinct_fieldPoint_length_le` states that a point of
`E.tupleDistinctScheme n` valued in any field of universe `u` implies
`n + 1 ≤ E.tupleLengthBound`. For each coordinate `i`, the proof takes the
unique relation arrow from coordinate `0` to coordinate `i`. These arrows
give elements of the type of lifts through `E.s` above the fixed zeroth
coordinate. Equality of two arrows implies equality of their targets.
The previously proved injectivity of the coordinates of a distinct tuple
then makes the assignment from `Fin (n + 1)` injective. The uniform finite
bound on field-valued lifts supplies the cardinal inequality.

`tupleDistinctScheme_isEmpty` proves that this scheme has no points if
`E.tupleLengthBound ≤ n`. A hypothetical scheme point gives its canonical
map from the spectrum of its residue field. Applying the preceding inequality
would give `n + 1 ≤ E.tupleLengthBound ≤ n`, a contradiction. Thus the
conclusion concerns all underlying points of the actual scheme, rather than
only rational points over a fixed field.

The provenance is derived from the bounded-fibre truncation argument in
Stacks Project, Tag 07S9, Lemma 68.8.4, and the distinct related tuples of
Tag 0BBN, Lemma 68.8.3. The retained originals are in the registered source
`stacks-stratification-2026-11-02`. The implemented proof uses the preceding
uniform affine étale field-point bound and Mathlib's residue-field map.
It constructs neither a symmetric quotient nor strata or a Noetherian
first level.
