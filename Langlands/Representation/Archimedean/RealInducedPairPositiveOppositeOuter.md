# The opposite outer parity in the positive crossed comparison

This internal construction compares the actual outer mixed sources of a
positive-inner pair and its negative-inner crossed pair, and constructs an
exact map from the second positive outer source onto the negative outer
quotient's kernel. It applies to every linked original pair with positive
absolute weights `L,M` and signed inner weight `H>0`.

Fix the original endpoint parities `sd=L%2,se=H.toNat%2` and write the
endpoints as `u,v,x,y`. The positive outer source has the remaining characters
at exponents `x,v`, with parities `H%2,1`. For the crossed pair
`lowerData,upperData` at `crossedIndex`, the negative construction instead
has the remaining characters at exponents `v,x`, with parities
`0,(H+1)%2`. Thus both signs change as well as the order.

`flipParity` adds one modulo two. `oppositeOuter` is the original
`DistantParity.outerPiece` with both quotient parities flipped.
The lemmas `crossed_v` and `crossed_x` identify the actual remaining
characters, including signs. `crossed_outer` identifies the outer induced
datum: its weight is unchanged, and its mean exponent ignores the endpoint
parities. Consequently `crossed_companion_eq_opposite` identifies the
negative crossed companion source exactly with `oppositeOuter`.
`negative_source_eq` records the target source with its two remaining
characters in the reversed order.

The generic construction `RealInducedPairNegativeOuterKernel` supplies an
actual exact `kernelGenerator` from its companion source, with range exactly
the kernel of `NegativeOuterQuotient.replacementQuotient`. The crossed pair
is linked and has signed inner weight `-H<0`. Transport the generic map
along the proved companion-source equality. This gives the `kernelGenerator`
of this module, from `oppositeOuter` into `negativeOuter`. Equality transport
is exact and surjective, so it preserves the full range equality.

The second positive outer source preserves exponent support and has
squared-weight sum `P²`, with `P=L+M+H`. Thus it is an allowed strictly
heavier adjacent piece. The opposite quotient parities also satisfy the
outer reducibility parity.

`RealInducedPairPositiveOppositeOuterStatement` asserts this allowed-source
property and existence of the actual exact map with its range equal to the
specified negative crossed quotient kernel.
`realInducedPairPositiveOppositeOuter` proves the statement.

This identifies a source-level kernel map and explains the appearance of a
second outer parity. It does not identify its composite into the original
target with any incoming crossing word, prove either remaining kernel-image
containment, or prove `RealInducedInducedFiltrationStatement`.
