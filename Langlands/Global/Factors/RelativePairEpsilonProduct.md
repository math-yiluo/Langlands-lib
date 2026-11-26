# JPSS epsilon products of unitary supercuspidal blocks

`PadicSupercuspidal.unitarySupercuspidalDatum` forms a square-integrable Langlands datum from unitarizable supercuspidal blocks with all exponents zero. Essential square integrability follows from `Classification.unitarizableSupercuspidal_isSquareIntegrable`, and `realPowerTwist_zero` gives the unitary block condition. An irreducible representation equivalent to the full normalized induction is a Langlands quotient of this datum by the inverse of the equivalence.

`isUnitaryPairEpsilonFactor_of_isLanglandsPairEpsilonFactor` specializes `IsLanglandsPairEpsilonFactor` to these data and obtains a product of block certificates. `eq_sum_blockBasisClass_of_equiv_productInduced` identifies the two witnessed supports with the sums of the block classes. Uniqueness of basis epsilon certificates and bilinearity of `epsilonHom` identify the product with the lattice factor required by `Langlands.Global.PoleComparison.RelativeIsometryFactorStatement`.

The product over Langlands blocks is the one in Henniart (2002), §2.8, printed p. 596.
