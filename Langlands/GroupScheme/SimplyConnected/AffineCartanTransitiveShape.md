# The full shape of a vertex-transitive Cartan matrix with a positive left kernel

This internal matrix lemma supplies a support step for the affine-diagram argument
over local fields. It works for an arbitrary finite index type, including the empty
type, and has no hypotheses about groups, fields or buildings.

## Meaning and provenance

`Langlands.GroupScheme.AffineCartan.IsVertexTransitive B` says that for any two
indices `i` and `j` there is a permutation `σ` with `σ i = j` preserving every
entry: `B (σ k) (σ l) = B k l`.

The two sum lemmas assume this predicate and an integral vector `m` whose entries
are strictly positive and which lies in the left kernel, `Matrix.vecMul m B = 0`.
Every row sum and every column sum of `B` is then zero.

`shape_of_isVertexTransitive` also assumes diagonal entries `2`, nonpositive
off-diagonal entries, and symmetric support, expressed by
`B i j = 0 → B j i = 0`. It proves that the **entire** matrix is symmetric,
every off-diagonal entry is `0`, `-1` or `-2`, and, if `i ≠ j` and
`B i j = -2`, every other vertex `k` satisfies `B i k = B j k = 0`.
Symmetry also gives the corresponding zero columns. Thus such a pair is an
isolated component. No connectedness or nondegeneracy hypothesis is assumed.

The argument generalizes intermediate calculations in the published module
`Langlands.GroupScheme.SimplyConnected.AffineCartanTransitive`, by Workers 158
and 5662. That module uses a distinguished extra vertex and a nondegenerate
principal block to classify the block as type `A`. Here those hypotheses are
unnecessary because the conclusion concerns the full matrix's entries, without
classifying its components.

The motivation is the transitive affine diagram in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), proof of Theorem 10.3.1,
printed pp. 391–392 / PDF pp. 422–423. This is a derived, elementary matrix
argument, rather than a formalization of the affine-root-system classification
in Proposition 6.4.8. In particular it excludes any off-diagonal entry `-4`,
such as the nonreduced rank-one relative affine matrix, as soon as the listed
matrix hypotheses are supplied.

## Implemented proof

Entry-preserving permutations show that the row sums are all equal. Pairing
them with the left kernel vector gives their common value times `∑ i, m i`
equal to zero. When an index is supplied the type is nonempty, so the latter
sum is positive, and each row sum vanishes. Column sums are likewise equal,
and their total is zero by the row calculation; division by the nonzero
integer cardinality proves that each column sum vanishes.

For distinct `i,j`, split their two entries off the sum of row `i`. The remaining
entries are nonpositive, so `B i j ≥ -2`. If it is `-2`, every remaining
off-diagonal entry in that row is zero. Symmetric support then makes every
remaining entry in column `i` zero; its column sum forces `B j i = -2`.
The same row argument at `j` proves isolation of the pair.

Integrality now gives the three possible off-diagonal entries. Opposite entries
vanish together and equal `-2` together. In the remaining case both are `-1`,
which proves symmetry of the full matrix.

## Application obligations

This module constructs no affine root system, stable chamber, positive marks,
or Cartan comparison. In particular it does not prove
`LocalAnisotropicAffineDiagramStatement` or splitting over the maximal
unramified extension. Those application obligations remain open.
