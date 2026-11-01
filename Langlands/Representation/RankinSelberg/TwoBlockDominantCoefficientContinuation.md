# Actual model coefficient clearing and denominator bounds

This internal contribution specializes finite spectral clearing to actual
equal-rank and unequal-rank determinant coefficients. It gives the polynomial
divisibility direction used in the dominant-rank L bound. Uniform finite
clearing is an explicit premise; this module does not establish the first-block
equations or either final dominant-rank gamma/L proposition.

All declarations are in
`Langlands.RankinSelberg.DominantRankTransport`. The field and the two
representation carriers retain independent universes. The residue cardinality
and normalized absolute value are those of the canonical topological data of
the supplied p-adic field. The additive character and measures are supplied.

`EqualModelFiniteClearing` says that, for every pair of functions in the
specified coefficient models and every Schwartz–Bruhat row test, the ordinary
polynomial `A`, embedded in the Laurent polynomial ring, sends the actual
equal-rank coefficient series to the coefficient series of a finite Laurent
polynomial. `StrictModelFiniteClearing` says the corresponding thing for the
actual unequal-rank series with rectangle dimensions `j,k`. The latter larger
rank is `n + (j + k + 1) + 1`; the smaller rank is `n + 1`, so this case is
strict even when either rectangle dimension is zero.

`equalRank_hasBilateralSpectralExpansion` takes genuine absolute convergence
of the equal-rank integral on a right half-plane and applies
`equalRankSliceExpansion` point by point on that half-plane. It yields
`HasBilateralSpectralExpansion` for the actual integral as a function of its
complex parameter. `unequalRank_hasBilateralSpectralExpansion` does the same
using `unequalRankSliceExpansion_of_converges` and the actual product-space
convergence predicate. It requires the supplied rectangle measure to be
`SFinite`. Neither theorem infers convergence from a total integral equality.

`equalModelFiniteClearing_polynomialDivisibility` assumes full Whittaker type
of both representations, the appropriate standard and inverse characters, and
nonzero supplied functionals. It also assumes an intrinsic equal-rank L
polynomial `P`, a nonzero clearing polynomial `A`, and
`EqualModelFiniteClearing`. Its conclusion is exactly

```text
∃ (Q : Polynomial ℂ) (e : ℕ), X ^ e * A = Q * P.
```

The proof rewrites the entire intrinsic set `equalRankZetaValues` into the
specified coefficient models using `equalRankZetaValues_eq_model`. Full
Whittaker type supplies scalar multiplicity one through `eq_smul`, so this
rewrite includes images of every functional, including the zero functional.
Each member of the rewritten set already carries actual convergence on a
right half-plane and rational continuation. The preceding expansion theorem
and the clearing premise supply
`normalizedGenerator_divisibility_of_clearedExpansions`, which gives the
displayed polynomial equation. No additional convergence premise is imposed
on the intrinsic zeta values.

`strictModelFiniteClearing_polynomialDivisibility` follows the same route for
`unequalRankZetaValues_eq_model` and `IsUnequalRankLPolynomial`, retaining the
exact supplied quotient and rectangle measures and the `SFinite` rectangle
measure premise. The larger and smaller representations have full Whittaker
type at their respective ranks. Its conclusion has the same polynomial
orientation.

The provenance is internal and derived: the implementation combines the
published intrinsic-to-model equalities and determinant-slice expansions with
the generic normalized-generator clearing theorem in
`TwoBlockDominantRationalNumerators`. It introduces no new source assertion.
It proves neither uniform clearing for an induced pair nor a symmetric factor
certificate; those are separate obligations in the dominant-rank assembly.
