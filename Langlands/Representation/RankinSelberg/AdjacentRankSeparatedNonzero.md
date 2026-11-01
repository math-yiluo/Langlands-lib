# Nonzero separated adjacent continuations

Worker 486. This internal composition defines the Prop-valued
`AdjacentRankNonzeroSeparatedContinuation`. It states the existence of an
actual separated square/row Schwartz tensor, a block model vector, an
ambient model coefficient given by that tensor, an inverse-character test
model vector, and a nonzero rational continuation of their corank integral.

`adjacentRankImage_exists_nonzeroSeparatedContinuation` proves this
existence from whole-function image equality for the actual adjacent model
map and one nonzero corank continuation somewhere in that image. Its
hypotheses retain full Whittaker type of the block, ambient and test
representations, specified functionals, nonzeroness of the ambient and test
functionals, the supplied self-dual scalar Haar measure and a compatible
quotient measure. The field and the three carrier universes are independent.
No irreducibility hypothesis is used.

Whole-function image equality allows each value of the actual adjacent
model map to be lifted to the ambient coefficient image. Equality of the
underlying functions proves that these choices form a linear map. The
published unequal-rank analytic theorem supplies the bilinear rational
continuation family for block zero. Its actual integrals equal the corank
integrals because the rectangular variable has zero rows. Composing that
family with the linear lift, with the given inverse-character test vector
fixed, gives a linear rational-valued map on the actual adjacent test space.
Rational-continuation uniqueness identifies its value at a preimage of the
supplied ambient coefficient with the specified nonzero rational function.

If every separated tensor had zero value under this map, tensor-space
induction and the finite square/last-column expansion of every rectangular
Schwartz function would force the map to vanish everywhere. This contradicts
the supplied nonzero continuation. Choosing a separated tensor where it is
nonzero proves the stated conclusion, with the continuation from the same
bilinear family and the actual lifted model coefficient.

The provenance is internal composition of actual model-image equality,
Schwartz tensor expansion, the published unequal-rank continuation theorem
and continuation uniqueness. The result retains image equality and the
initial nonzero continuation as explicit premises. It constructs no gamma
factor by itself; its purpose is to select a nonzero separated integral for
the subsequent comparison with the matched finite-product equation.
