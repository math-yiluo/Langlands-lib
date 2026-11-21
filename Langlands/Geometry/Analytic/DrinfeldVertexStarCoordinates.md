# Coordinates of a vertex star and its thickening

`VectorNorm.logBasisWeights ν b i` is `log (ν (b i))`. It preserves
nondecreasing order of the weights because basis vectors are nonzero.
If `ν` is adapted to the basis `b` and `b` is normalized for a reference
norm `μ`, then the multiplicative distance `distRatio ν μ` is the
largest weight of `ν` divided by the smallest. The two directed ratio
suprema are attained at the last and first basis vectors, respectively.
Thus distance less than `q > 0` is equivalent to log-width less than
`log q`.

## The actual nearest-vertex star

Let `ϖ` have maximal nonzero absolute value below one and put `q =
‖ϖ‖⁻¹`. Suppose `w_i = ν (b i)` is nondecreasing and the distance to
`μ` is less than `q`. `mem_vertexStar_iff_isSortedStar` says that `⟦ν⟧`
is in the Library's star of `⟦μ⟧` exactly when every adjacent log-gap
is at most the external gap `log q − (log w_d − log w_0)`.

For necessity, a strict gap after index `i` gives a rounded ball norm
with scale `w_i`. Its weights are 1 through index `i` and `q` afterwards.
Its distance to `ν` is at most `q w_i / w_(i+1)` by the common adapted
basis ratio bounds. Comparing with this vertex and taking logs gives
the gap test. A zero gap satisfies it by the width hypothesis.

For sufficiency, a competing vertex at distance at least `q` cannot
be closer. A closer competitor has a lattice representative equal to
a rounded ball norm of `ν`, hence its weights in `b` are nondecreasing.
If consecutive weights are different, their ratio is at least `q`
by maximality of `‖ϖ‖`. Evaluating the two directed suprema at that
pair gives a distance at least `q w_i / w_(i+1)`, which is at least the
distance to `μ` by the gap test. If every consecutive pair is equal,
comparing the first and last weights gives the required lower bound
instead. The comparison is with all vertices, not just a prescribed
list of vertices in an apartment.

## The open neighbourhood

Over a proper ultrametric field, with `μ` a lattice norm and the same
basis and strict distance bound, `mem_vertexNbhd_iff_sortedStarIneq`
identifies membership of `⟦ν⟧` in `vertexNbhd ⟦μ⟧ ε` for `ε > 0` with
all the strict tests of [`DrinfeldSortedStar`](DrinfeldSortedStar.md).
For necessity, a point of the star witnessing membership is itself at
distance less than `q` from `μ`, by the nearest-vertex gap bound. Choose
its own sorted adapted basis normalized for `μ`. The sorted weight
comparison bounds the spread of the differences between the two log
weight tuples by the strict thickness bound, even if the bases differ.

Conversely the tests give sorted log weights satisfying the star gap
condition and the required strict spread bound. These weights have
width less than `log q`: otherwise all adjacent increases are
nonpositive and the total width is nonpositive, a contradiction.
Exponentiating them defines a weighted norm in `b` with the given log
weights. It is in the actual star by the first criterion, and its
distance to `ν` satisfies the strict bound by the common-basis formula.

This is an internal derivation from the norm model and the rounded-ball,
sorted weight, and real tuple lemmas. It supplies the building-side
coordinates needed for compact analytic differences; it does not
construct any analytic domain or prove a general simultaneous apartment
theorem.
