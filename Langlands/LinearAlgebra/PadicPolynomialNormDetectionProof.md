# Detecting a p-adic polynomial by norms of resultants

This module proves
`Langlands.LinearAlgebra.padicPolynomialNormDetection`, whose type is exactly
`Langlands.LinearAlgebra.PadicPolynomialNormDetectionStatement`.
For every prime `p`, monic polynomials `P,Q` over the actual field `ℚ_[p]`
of equal natural degree agree if the norms of their resultants with every
integer polynomial agree. No integrality or separability condition is
imposed on `P` or `Q`.

The proof is internal mathematics assembled from the Library's analytic
and root-count lemmas. Its source context is Milne, *Abelian Varieties*,
author revision of January 2, 2022, Lemma 12.10 on p.23. Milne states the
lemma in terms of products over roots and cites Lang for its proof. The
implemented proof below is not claimed to be that cited proof.

`coefficientResultant P n` expresses the resultant as a multivariate
polynomial in a bounded test-coefficient vector. Its evaluation lemma
follows from functoriality of the Sylvester determinant. The helper
`resultant_monic_degree` shows that a monic first argument makes increasing
the degree bound on the second argument harmless.

The helper `norm_resultant_eq_of_integral_coeffs` extends the assumed
integer-test norm equality to test polynomials over `ℚ_[p]` whose
coefficients have norm at most one, wherever the resultant with `Q` is
nonzero. It applies `norm_eval_eq_of_natCast` to the two coefficient
resultants. Natural coefficient tests are among the assumed integer tests;
the existing density theorem then supplies all integral p-adic coefficient
vectors.

`resultantLine P F` is the polynomial in `t` whose value is
`resultant P (F + C t)`. After mapping to an algebraic closure, the monic
resultant product formula identifies it with the product of `X + C (F(q))`
over the roots of `P`, with multiplicity. This product is monic and hence
nonzero. For nonzero `c`, `rootMultiplicity_resultantLine` identifies its
order at zero for `F = C c * π` with `rootCount L P π`, since multiplication
by `c` does not change whether the test polynomial vanishes at a root.

For each monic irreducible test `π` of degree at most `P.natDegree`, the
existing `exists_integral_multiple` supplies nonzero `c` such that
`C c * π` has integral coefficients. Adding `C t` preserves that condition
when `‖t‖ ≤ 1`, by the p-adic nonarchimedean inequality. The extended norm
equality and `rootMultiplicity_zero_eq_of_norm_eval_eq` therefore give
equal orders at zero of the two resultant lines. Their root-count
interpretations give equal counts for `P` and `Q`. Finally,
`eq_of_rootCount_eq` concludes `P = Q`; the assumed equal degrees put both
polynomials within the same bound.

All norm and continuity arguments take place over `ℚ_[p]`. The algebraic
closure is used only for polynomial identities and root counts; no choice
of an extended norm on that closure is needed. The theorem proves this
general supporting lemma and does not itself prove the geometric
endomorphism trace-comparison target.
