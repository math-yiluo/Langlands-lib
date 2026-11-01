# Common compact support of corank determinant slices

This internal derived module supplies a concrete compact container
`CommonLevel.diagonalAnnulusImage` and proves
`CommonLevel.corank_common_compact_support`. It derives the common-support
part of the corank extraction of the argument in JPSS (1983), Section 4.5,
printed pages 408–409. The general family formulation is derived content,
not a verbatim assertion of the original.

The assumptions are a canonical p-adic field with any of its supplied
topological data, a standard-character Whittaker family on the larger group
`GL_(r+2)`, and one open right level for the whole family. Compactness of the
level and parameter analyticity are not needed here. For each determinant
order `m`, the module produces one compact subset of the actual quotient
`N_(r+1) \ GL_(r+1)` containing the supports of the literal slice indicators
of all corank integrands. The same subset works for every parameter, every
inverse-character test function, and every spectral variable.

The implemented proof first splits a small-group Iwasawa decomposition into
an actual upper unipotent, an arbitrary diagonal of field units, and an
integral factor. Appending a final identity coordinate changes that diagonal
to `Fin.snoc a 1`; the inclusion preserves the integral subgroup.
The uniform simple-root bound from `CommonLevelRootSupport` therefore bounds
every adjacent ratio of this appended diagonal. Reverse induction starting
from its final entry one bounds every smaller diagonal entry above, without
any central-character assumption.

On a fixed determinant-order slice the product of the normalized absolute
values is `q^(-m)`, because the unipotent determinant is one and the integral
factor has determinant absolute value one. The common upper bound then
gives a positive lower bound for each diagonal entry. The diagonal entries
range over compact annuli in field units. The continuous image of the
product of these annuli and the compact integral subgroup gives
`diagonalAnnulusImage`. Left unipotent covariance shows that every nonzero
slice-integrand value maps into this set.

The proof includes `r = 0`: the appended diagonal has two entries and its
final simple root bounds the single smaller entry. There is no nonzero
functional, vector, or coefficient assumption. The module proves a support
bound, not integrability, analytic dependence, or a factor specialization.

Source: H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions* (1983), registered as
`jpss-1983-rankin-selberg`. The compact-annulus argument reuses the published
`WhittakerRowSliceCompactSupportProof`, whose row bound here is replaced by
the appended identity coordinate.
