# The actual dual integral in real corank one

`RealJacquet.RealUnequalDualIntegralAdjacentStatement` and its proof
`realUnequalDualIntegral_adjacent` identify the Library's real dual block
integral for ranks `r+2` and `r+1` with the ordinary unequal-rank integral
of the two pointwise `dualFunction`s. They use the original compatible
quotient measure, with no additional scalar and for every spectral `s`.
This is an internal specialization of the Library definitions, analogous
to `ComplexLocalAdjacentIntegrals`, not a new analytic continuation result.

The rectangular matrix has zero rows, so it equals the zero matrix.
`RealUnequalPairConvergence.rectangularPoint_zero` identifies the resulting
block point with the upper padded group element. The unfolding Weyl element
is the identity: its only nontrivial candidate block is the size-one long
Weyl element, which has entry one. These facts give the kernel equality
`realUnequalDualKernel_adjacent`.

The self-dual measure contributes no scaling in dimension zero: the product
of no row measures is the Dirac mass at zero. On the product with the
quotient, this gives the pushforward of the quotient measure by adjoining
the empty rectangle. The `integrable_realUnequalDualKernel_adjacent_iff`
lemma uses that measurable embedding to compare absolute integrability.
The equality of the actual iterated integrals is then obtained by evaluating
the inner Dirac integral. The equalities do not assume the Whittaker model
conditions and do not assert that either integral converges at every `s`.
