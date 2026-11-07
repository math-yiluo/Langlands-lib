# Actual lowering endpoints along simple-reflection words

This derived unit works over a field `k : Type u`, with an affine group scheme
`G` and a supplied split pinning `p`. Its first constructions use supplied
actual rational simple-reflection representatives `s`, and a supplied family
`xm` of additive group-scheme maps indexed by the simple roots. Define
`W([])=1` and `W(i::l)=W(l)s(i)`. The corresponding torus automorphism acts
on characters by exactly `PositiveRootWord.wordAut`. Define the list of
lowering maps recursively by putting `conjugateMap (xm i) (W(l))` before
the list for `l`. This is the same tail-first convention as `PositiveRootWord`.

If every original map is torus-equivariant with character minus its simple
root, the conjugated maps have characters minus the corresponding successive
roots. `reflectionWordLoweringMaps_equivariant` expresses this as a
`List.Forall₂` statement. Each equivariance law quantifies over every relative
test scheme, every torus point and every additive scalar; it is not limited
to field-valued points. These constructions and this transport identity
require neither positivity of the word nor a highest-weight representation.

For a matrix representation on `n → k`, with `n` finite, and a natural
number `m`, `reflectionWordCoefficient` is the ordered product of the
original degree-`m` divided-power operators of these actual conjugated maps.
Given a vector `v` and a unit endpoint equation
`D_i(m)v=c_i rho(s(i))v` for each original simple map, the product telescopes:
it sends `v` to a unit times `rho(W(l))v`. Induction uses the actual
conjugation identity for divided powers and preserves the factor order.
No highest-weight or nonzero-vector hypothesis is needed once these
single-root endpoint equations are supplied. The same product is
`OrderedAdditiveProducts.orderedCoefficients` at any exponent tuple whose
entries all equal `m`; this is the coefficient of the genuine ordered
polynomial action, without permuting its factors.

The highest-weight specialization additionally assumes that `k` is infinite,
the root index is finite, the integral coroot span is the whole cocharacter
lattice, and `rho` satisfies the original `IsHighestWeight` condition at
`lam`. For each simple root, supply opposite torus-equivariant additive maps
and their linked coroot relation over every relative test scheme. Require
the simple root to be strictly positive on the polarization of integral
rho, and require its coroot pairing with `lam` to equal the natural number
`m`. The imported single-root endpoint theorem then supplies the required
unit equations for every nonzero vector in the highest-character space.

For `lam = m • rho`, the simple pairings equal `m` and the required positivity
follows from the base. `exists_highestWeight_positiveWord` derives the linked
maps and all-test relations from the pinning and obtains a finite positive
word whose successive roots are distinct and enumerate every positive root.
For supplied `s`, its resulting coefficient is nonzero on every nonzero
original highest vector: the telescoped unit is nonzero and the rational
word matrix is invertible.

Finally `exists_highestWeight_nonzero_orderedCoefficient` also chooses
the actual rational simple-reflection representatives from the pinning's
root datum. It supplies the same root enumeration and all-test equivariance,
and states nonvanishing directly for the existing ordered polynomial
coefficient at every tuple with all entries `m`. It adds no separate
representative or root-cell existence premise. It retains infinitude,
finite root index, full coroot span, and the supplied highest-weight
representation at `m • rho`.

The provenance is the imported positive-root word construction, actual
normalizer action, conjugation of original additive coefficients, and
single-root highest-weight endpoint theorem. No external source is used.
This unit does not construct a highest-weight representation or an induced
space, prove the dimension of the whole induced space, or identify the
conjugated maps with scheme coordinates on the full radical.
