# Fixed centralizer intersections and dynamic maximality

This internal construction uses the actual pullback intersection of a subgroup
`j : H → G` and a closed representative `z : Z → G` of the dynamic centralizer
of a cocharacter `χ`. Assume that `j` is monic and its all-test range is normalized
by the range of `χ`. The first intersection projection represents the fixed
subgroup for the published normalized conjugation action on `H`.
`subgroupCentralizerFixedModel` packages that actual group scheme, projection,
representation proof and closedness proof.

The representation proof identifies normalized conjugation with ambient
conjugation after composition with the monomorphism `j`. The universal fixedness
equation is exactly the universal orbit equation defining the dynamic centralizer.
The pullback universal property identifies its solutions with the range of the
first projection on every test scheme, including nonreduced tests.

Over an arbitrary field, smoothness of the intersection follows for smooth affine
`H` by identifying the acting multiplicative group with the diagonalizable group
with character lattice `PUnit → ℤ` and applying the published diagonalizable
fixed-subgroup smoothness theorem. Independently, normalization of the range of
`j` by the range of `z` implies normality of the second projection's range in `Z`,
by the pullback universal property and the conjugation equation on all tests.

These are internal deductions from existing Library constructions and theorems.
Combining them with the split limit in `Dynamic.SubgroupLimit` proves the following
maximality result over an arbitrary field. Suppose `H` is smooth, affine, connected
and unipotent, its range is contained in `P(χ)`, and its range is normalized both by
the range of `χ` and by the range of `z`. Assume the ambient group is separated and
`Z` has trivial unipotent radical in the exact sense of
`HasTrivialUnipotentRadical`. The second intersection projection is closed,
smooth, connected, unipotent and normal. Applying that predicate makes its range
trivial on every test. The dynamic limit of each `H`-point factors through this
projection, so that limit is the identity. Thus the whole range of `H` lies in
`U(χ)` on the original test scheme, without a covering or a reducedness assumption.

The normal-subgroup corollary takes any closed representative `p : P → G` of
`P(χ)` in an affine group and any smooth connected normal unipotent closed subgroup
`v : H → P`. Normality implies that the ambient range of `v ≫ p` is normalized by
the range of `p`; both the cocharacter and its centralizer lie in that range.
Closedness gives the required affineness of `H`. The preceding theorem therefore
proves `range (v ≫ p) ≤ U(χ)` under the stated trivial-radical hypothesis on `Z`.

The file does not establish triviality of the centralizer's radical, unipotence
of `U(χ)`, their base-change comparisons, the full geometric radical identification,
or the final semistandard intersection theorem. It supplies the indicated
maximality implication for use with independently proved structural results.
