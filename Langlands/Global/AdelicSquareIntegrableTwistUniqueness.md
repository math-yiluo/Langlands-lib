# Uniqueness of the twisted square-integrable part of a Levi pairing

Delorme defines the extended pairing \(p_Q\) in terms of the square-integrable part of the first
argument after (3.7). The regularized pairing in (7.9)–(7.12) uses this construction on finite sums
of twists. `SquareIntegrableTwistPartUniquenessStatement` gives the pointwise uniqueness needed
when presenting this part with finite labels, such as Weyl labels. The two label sets may have
different types, and several labels may give the same twist parameter.

Suppose \(A_1\) and \(A_2\) are finite sums of twists of forms in \(A^2_Q\), for the same
Iwasawa compact and parabolic, and both \(f-A_1\) and \(f-A_2\) are orthogonal to \(A^2_Q\) on
every positive split-component slice. The submodule `squareIntegrableOrthogonalSubmodule`
implies that \(A_1-A_2=(f-A_2)-(f-A_1)\) has the same orthogonality, including integrability
of each test pairing. The proof reindexes the disjoint sum of the two finite label sets by
`Fin` and uses the corresponding positive and negative height-exponential coefficients.
This gives a `HasSquareIntegrableHeightExpansion` of the difference. Applying
`eq_zero_of_squareIntegrableHeightExpansion_of_orthogonal` gives \(A_1=A_2\) as functions on
\(G(\mathbb A)\).

`IsSquareIntegrableTwistDecomposition.twistSum_eq` specializes the first presentation to the
parameter-indexed `IsSquareIntegrableTwistDecomposition` used by the regularized pairing.

Source. P. Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023),
109107, registered as `delorme-2023-spectral-theorem-langlands`. Published PDF SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`. See §3.4, after (3.7) on
printed p. 15, and (7.9)–(7.12) on printed p. 25.
