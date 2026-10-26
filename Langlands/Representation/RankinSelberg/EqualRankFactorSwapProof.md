# Equal-rank pair-factor exchange

The theorem `Langlands.RankinSelberg.equalRankFactorSwap` proves the closed
proposition `Langlands.RankinSelberg.EqualRankFactorSwapStatement` in the
three independent universes `uF`, `uV` and `uW`.

The implemented helper `equalRankZetaValues_swap_inverse` exchanges the two
coefficient functions by retyping their actual Whittaker covariances at the
inverse additive character. Multiplication commutes pointwise on the actual
left-unipotent quotient, so the existing half-plane convergence and rational
continuation witnesses survive unchanged. This uses no factor-existence or
Whittaker-type hypothesis.

The implemented `isEqualRankLPolynomial_swap_inverse` applies this equality to
the normalized-generator relation. The p-adic helper
`isPadicPairLPolynomial_swap_equalRank` then proves the fixed-character
L-polynomial iff for arbitrary actual representations of the same positive
rank. At each compatible quotient measure, the published
`characterChangeCompatibleMeasure` supplies its transport law and
`isEqualRankLPolynomial_characterChange_normalized` restores the original
character using scale `-1`. The compatible-measure existence witness and
universal quantifiers are retained. The supplied additive Haar measure is
unchanged; no self-duality or Whittaker-type hypothesis is needed for this
L-only helper.

This is internal proof infrastructure for JPSS (1983), Section 2.12, printed
page 403 (PDF 38), registered source `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The exact theorem `equalRankFactorSwap` assembles this L-polynomial result
with the epsilon and gamma transport in `EqualRankSwapFactors`. Those two
proofs translate both functionals by the minus-one diagonal, exchange them,
and retain the actual Fourier pair at the original character and supplied
Haar measure. The dual integral gains alpha^n beta^n, which converts the old
second-model scalar beta^n to the new scalar alpha^n because beta squares
to one on a nonzero model. Original rational value sets coincide and dual
value sets have the same Laurent span. The proof preserves every compatible
quotient measure and nonzero-functional test; it uses no analytic or
factor-existence premise and makes no contragredient identification.

The supporting modules contain derived constructions and lemmas used only
to establish this exchange. All factor relations and the target proposition
are imported unchanged. In particular this is a transport of any supplied
certificate, not an assertion of factor existence.
