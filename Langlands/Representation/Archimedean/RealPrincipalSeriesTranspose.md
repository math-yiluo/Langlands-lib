# The compact Haar transpose of a scalar principal-series embedding

`RealPrincipalSeriesTransposeStatement` takes a real `(𝔤, K)`-module and
an algebraic compact and Lie map `B` into the compact-finite vectors of a
scalar real principal series. The list of inverse inducing characters
defines a second scalar principal series. The transpose sends a
compact-finite vector `f` of this second series to the functional

\[
     v\longmapsto\int_{O(n)} f(k)(Bv)(k)\,dk,
\]

where Haar measure has mass one. The functional is compact-finite for
the algebraic dual action. The transpose intertwines the actual orthogonal
and real matrix Lie actions with the compact-finite contragredient. The
hypothesis on `B` is `IsRealStandardEmbedding`, which records compact and Lie
intertwining. No injectivity of `B` is needed to construct the transpose.

## Proof

Normalized Haar measure on the orthogonal matrices pushes forward to
normalized Haar measure on their subgroup of real matrix units. Transport
through the continuous group equivalence gives `pairing_eq_orthogonal`.
This aligns the pairing with the compact profiles on the orthogonal group.

Compose `RealPrincipalSeriesDuality.pairing` with `B` in the second
variable. The original compact covariance of `B` and right invariance of
the pairing make the resulting map equivariant for the algebraic dual
compact action. Consequently the image of a compact orbit span has finite
dimension. For real Lie directions, the two character lists are pointwise
inverse by `realPositionCharacter_map_inverse_mul`. The derivative
invariance of the pairing then gives the negative transpose identity, in
the convention of `RealContragredient.dualLie`.

The calculation is the transposition step of the quotient-form reduction
in `RealPrincipalSeriesQuotientReduction`, with the compact integral kept
explicit for subsequent analytic estimates.
