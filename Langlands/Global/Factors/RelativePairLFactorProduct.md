# JPSS L-products of unitary supercuspidal blocks

`PadicSupercuspidal.isUnitaryPairLFactor_productInduced` identifies the virtual L-factor of the two sums of the block classes with the inverse L-polynomial of the two normalized inductions. `Classification.unitarizableSupercuspidal_isSquareIntegrable` gives square integrability for the blocks. `RankinSelberg.TemperedLFactorStatement.blockShape` applied to `RankinSelberg.temperedLFactor` then gives the product of block polynomials. Uniqueness of the symmetric polynomial and bilinearity of `unitaryPairLHom` identify the two evaluations.

`eq_sum_blockBasisClass_of_equiv_productInduced` uses `glSupercuspidalSupportUniqueness` to express a witnessed support of a representation equivalent to such an induction by the corresponding sum of block classes. `isUnitaryPairLFactor_of_equiv_productInduced` transports the pair L-polynomial across those equivalences.

For self-dual measures, `IsUnitaryBasisPairLPolynomial.change` uses `supercuspidalUnequalRankLFactor` in unequal ranks and `supercuspidalEqualRankLFactor` in equal ranks. The equal-rank product is determined by the same finite set of unramified twists for both characters. This gives `IsUnitaryPairLFactor.change` on virtual classes.

The block product and the supercuspidal formulas come from Jacquet–Piatetski-Shapiro–Shalika (1983), Propositions (8.4) and (8.1), pp. 451–452 and 443. They supply the automorphic L-factor computation for `Langlands.Global.PoleComparison.RelativeIsometryFactorStatement`.
