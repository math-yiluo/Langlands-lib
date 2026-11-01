# Actual unequal-rank determinant coefficients

This internal deduction supplies the determinant-coefficient interface for the
published `unequalRankIntegral`. It uses the actual `unequalRankIntegrand`,
normalized determinant weight, and generic determinant-slice partition proved in
`EqualRankSliceExpansionProof`. It makes no new claim from the literature.

`unequalRankAverage` integrates the actual rectangular variable first, using the
supplied Borel measure. `unequalRankSliceCoefficient` restricts that average at
parameter zero to the determinant slice and integrates against the supplied Borel
quotient measure. The unequal-rank normalization remains inside the integrand at
zero: this definition does not drop its exponent `-(j+k+1)/2`. The larger
Whittaker rank is `n+(j+k+1)+1`, and the inverse-character rank is `n+1`.

The pointwise scaling theorem splits the determinant exponent into its value at
zero plus `s`. On determinant slice `m`, the second factor is exactly
`spectralPoint q s ^ m`, with `q` the canonical residue cardinality. This factor
does not depend on the rectangle variable. Pulling it through the inner
integral gives the average scaling law, and pulling it through the restricted
outer integral gives `setIntegral_unequalRankAverage_determinantSlice`. Both
identities use totalized Bochner integrals and require no convergence.

The spectral factor is nonzero. The scaling law therefore gives the two-way
equivalence of genuine slice integrability between `s` and zero.
`unequalRankSliceExpansion` assumes integrability of the actual rectangle
average at `s`. Restriction gives integrability on every slice at `s`, and the
equivalence supplies slice integrability at zero. The published generic
partition theorems then give summability of the norms of the weighted
coefficients and their `HasSum` to exactly the actual iterated
`unequalRankIntegral`.

`unequalRankSliceExpansion_of_converges` starts instead from the published
product-space predicate `UnequalRankConverges`. The supplied inner measure is
assumed `SFinite`; the quotient measure need not be. Mathlib's
`Integrable.integral_prod_left` gives integrability of the average, so the
preceding theorem applies. No order of integration is exchanged.

All natural `j,k` are retained, including zero. The field uses its canonical
topology and valuation; both measures remain arbitrary supplied Borel measures.
In particular the results specialize to the supplied rectangular Haar measure
and compatible quotient measures without choosing or rescaling either. The
Whittaker functions are arbitrary, including zero, with no representation
irreducibility, full-type, nontrivial-character, or factor-certificate premise.
No lower support, outer convergence for arbitrary input, rational continuation,
functional equation, or dominant-rank gamma/L comparison is asserted.
