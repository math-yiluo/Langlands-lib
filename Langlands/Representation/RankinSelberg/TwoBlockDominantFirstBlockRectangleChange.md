# Original external rectangle change and exact column measures

`firstBlockColumnJoinEquiv` joins a pair of rectangular matrices with the
actual two-block column indices. It is a measurable equivalence for any
measurable scalar type. Its evaluation lemmas identify it with
`firstBlockColumns`, including on an arbitrary product argument. For a
topological field, a supplied additive Haar measure, and sigma-finiteness of
that scalar measure, `measurePreserving_firstBlockColumnJoinEquiv` preserves
the exact products defining the two rectangles. Composition therefore
preserves integrability for any normed additive target. With a real normed
space as target and integrability of the original function,
`integral_firstBlockColumns` gives the integral over the second column block
outside the first column block.

The remaining results use a supplied p-adic field, positive block sizes
`m 0 + 1` and `m 1 + 1` summing to `t + 1`, arbitrary natural `j,k`, an
arbitrary section of the actual normalized lower induction, supplied inverse
Whittaker functionals, an arbitrary equivariant test Whittaker function at
rank `t + (j+k+1)`, and an arbitrary complex spectral parameter `s`. The field
and block-carrier universes remain independent. No Whittaker-type,
irreducibility, functional-nonvanishing, or quotient-measure premise is used
in these local identities.

`unequalRankMatrix_rectangle_change` proves the actual matrix identity
`unequalRankMatrix j k g (X*g) =
rectangularUnipotent j k X * appendIdentity t (j+k+1) g`.
`firstBlockUpperValue_eq_rowScaled` consequently identifies the upper value
with the actual rectangular section integrand at `X*g`, multiplied by
`|det g|^j`. The section integrand uses the quotient determinant weight with
exponent `s - (j+k+1)/2`. The previously proved row substitution contributes
the inverse factor `|det g|^(-j)` for the exact supplied scalar Haar measure.
`integral_firstBlockUpperValue_original` cancels those factors and gives the
original rectangular section average. The separate theorem
`integrable_firstBlockUpperValue_original_iff` transports genuine
integrability under this substitution.

`integral_norm_firstBlockUpperValue_original` applies the same substitution
to the norm before integration. Taking the norm of the complex scalar
cancellation proves the corresponding positive real cancellation. Its
conclusion is the actual `rectangularSectionNormProfile` on the block
quotient, rather than the norm of a signed average. These two substitution
identities are identities of total Bochner integrals and assert no
convergence on their own.

Finally, the two `*_columns` theorems assume integrability of the original
rectangular section integrand at the supplied representative. The separate
integrability equivalence and exact measure-preserving column join justify
Fubini. They identify the iterated second-block/first-block column integrals
of the upper value and its raw norm with the original rectangle average and
real norm profile, respectively. The p-adic supplied scalar Haar is
sigma-finite by the existing local-field result.

This is derived coordinate and measure infrastructure for the first-block
calculation in Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg
Convolutions* (1983), §4.9, printed pp.416–418, and §4.10(2), printed p.419
(registered source `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`).
The arbitrary complementary `j,k` and explicit supplied-Haar norm formulas
are derived refinements of that calculation. This module establishes local
rectangle substitutions; global quotient Fubini, lower convergence, and the
Laurent functional equation require further results.
