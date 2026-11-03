# Proof of the Hilbert–Schmidt product diagonal identity

`Langlands.Analysis.OperatorIdeals.hilbertSchmidtProductTrace` targets
the full `HilbertSchmidtProductTraceStatement`, including absolute
summability of both diagonals and equality of the complex sums.

The first helper obtains Parseval as a `HasSum` identity from the actual
Hilbert-basis linear isometry to l2. The published arbitrary-index
Hilbert–Schmidt basis-independence theorem transfers the existential
predicate to any supplied domain basis. Applying Parseval in the
codomain and the nonnegative product-summability equivalence shows that
the squared matrix coefficients form a summable family on the product
of the two index types.

Apply that result to B and C, swapping the two indices for C.
The inequality `xy ≤ x² + y²` for the two nonnegative coefficient
norms bounds the norm of their complex product. Comparison gives
absolute summability of the full coefficient array.

The Hilbert-basis inner-product expansion and the actual adjoint identity
identify its row sums with the complex diagonal of `C.comp B` and its
column sums with that of `B.comp C`. Each diagonal norm is bounded by
the corresponding sum of coefficient norms, giving absolute diagonal
summability. Finally, absolute summability gives complex summability of
the coefficient array, and exchanging its two sums gives the required
identity.

Every sum is indexed by the actual arbitrary basis types. No countable
enumeration, separability, compact spectral theorem, trace-class product
theorem or assumed trace identity is used. The statement Markdown records
the original trace conventions and the internal provenance of this
intermediate result; this proof does not establish trace-class membership
or an automorphic trace formula.
