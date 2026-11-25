# Power sums and the alternating characteristic rational function

The declarations are in `Langlands.Cohomology.Weights`.

`rootPowerSum P k` sums the `k`th powers of the roots in the coefficient field
with their multiplicities. For a nonsplit polynomial over a general field it
counts only the roots in that field, not roots in a splitting extension. The
sum for `1` is zero, the sum for the product of two nonzero polynomials is
additive, and taking a natural power multiplies the sum by that exponent.

`multiset_eq_of_eventual_powerSums_eq` works over any characteristic-zero
field: two finite multisets of nonzero elements are equal if their power
sums agree from some exponent `N` onwards. The proof groups the two sums
on the union of their supports and takes the difference of their
multiplicities `c(z)`. After shifting the exponents by `N`, the weights
`c(z) z^N` annihilate evaluation of every monomial and hence of every
polynomial. The Lagrange basis polynomial at `z` isolates its weight, and
`z ≠ 0` and characteristic zero recover equality of the multiplicities.
`eq_of_monic_of_eventual_rootPowerSum_eq` applies this to monic complex
polynomials with nonzero constant term and reconstructs them from their roots.

`alternatingPolynomial_eq_zpow_of_eventual_powerSums` lets `H` be indexed by
`Fin (2*d+1)` and assumes that each `H i` and `P` is monic over `ℂ` with
nonzero constant term. If the signed sum of the power sums of `H i` equals
`a` times that of `P` for every exponent at least `N`, then
`alternatingPolynomial d H = (algebraMap ℂ[X] (RatFunc ℂ) P)^a` for the
integer `a`. The proof writes the alternating product as `E/O`, the ratio
of the even and odd products. For `a ≥ 0` apply reconstruction to `E` and
`P^|a| * O`; for `a ≤ 0` apply it to `E * P^|a|` and `O`. Mapping the
polynomial equalities into `RatFunc ℂ` gives the claimed quotient in both
cases. This does not require purity or semisimplicity.

## Provenance and scope

This is the algebraic step from (5.5) to (5.6) in R. E. Kottwitz, *On the
λ-adic representations associated to some simple Shimura varieties*,
Invent. Math. 108 (1992), §5, printed p. 663, with the product as in (6.1),
p. 664. Source `kottwitz-1992-lambda-adic-simple-shimura`, SHA-256
`749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
Kottwitz uses all positive Frobenius powers. The Lean version is an internal
algebraic formulation allowing an eventual identity and using power sums
of roots instead of traces of operators. Nonzero constant terms correspond
to invertible Frobenius. Neither the trace-to-root conversion nor the
geometric and spectral trace comparison is asserted in this module.
