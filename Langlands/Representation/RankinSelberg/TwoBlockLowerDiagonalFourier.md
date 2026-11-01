# Diagonal partial Fourier estimates for the lower integrand

This internal derived module proves a diagonal norm bound and endpoint support
conditions for the actual `TwoBlockLowerUnfolding.partialSection`. It uses the
supplied unitary additive character and supplied self-dual scalar Haar measure
throughout. It is a prerequisite for fixed-slice convergence, with no assertion
of outer absolute integrability or of a representation-independent threshold.

For arbitrary joined row coordinates, `join_vecMul_diagonal` splits diagonal
right multiplication into the two blocks. The theorem
`rowPartialFourierIntegral_diagonal` then applies the published determinant
change of variables for the first-block row Fourier integral. The resulting
factor is the inverse absolute value of the product of the first-block diagonal
entries. The Fourier argument is multiplied coordinatewise by the inverse
first block, while the untransformed argument is multiplied by the second
block. This identity applies to arbitrary functions and retains exactly the
scalar measure supplied in its hypotheses.

`exists_rowSchwartz_order_lower_bound` bounds below the valuation order of
every nonzero coordinate of any row where a given Schwartz–Bruhat function
is nonzero. To prove it, continuity of normalized absolute value bounds each
coordinate on the compact support. Comparing that bound with a power of the
residue cardinality gives a lower order bound; a finite sum makes it uniform
in the coordinates. `normalizedAbs_prod_inv_le_order_size` bounds the inverse
absolute value of a finite product of units by the residue cardinality raised
to the sum of the absolute values of their orders. Its proof uses the exact
normalized-absolute-value formula and the inequality between an integer and
its absolute value.

`partialSection_diagonal` specializes the generic change of variables to the
published positive two-block shape, first-block Fourier vector `zeta`, and
second-block vector `eta`, using p-adic scalar Haar scaling for the supplied
measure. `exists_partialSection_diagonal_bounds` combines this formula with
Schwartz–Bruhat closure of the first-block Fourier integral. It produces a
positive real constant `C` and a natural number `M` such that, for every diagonal
unit vector `d`,

- the norm of the partial section is at most
  `C * q ^ (sum j, natAbs (ord (d j)))`;
- a nonzero partial section forces the order of the original first-block
  first diagonal entry to be at most `M` and the order of the original
  second-block last entry to be at least `-M`.

Indeed, the transformed Schwartz function is evaluated at the joined row with
first component `zeta * d_first⁻¹` and second component `eta * d_second`.
Its uniform norm bound yields the displayed growth bound after enlarging the
first-block order sum to the full row sum. Its compact support bounds both
endpoint coordinates; those coordinates equal the inverse first endpoint and
the second endpoint respectively. No condition on the Fourier factor at
other rows is substituted for this actual evaluation.

`DiagonalBoundData` packages the positive constant, natural cutoff and both
certificates for the supplied partial section. The definition
`diagonalBoundData` chooses such a package from the proved existence theorem
under the same self-duality hypothesis. Its fields expose the estimates for
subsequent arguments without choosing a new Haar measure or changing the row
factor.

These are internal consequences of `TwoBlockRowPartialFourierSchwartz`, the
published row Fourier equivariance theorem, canonical p-adic Haar scaling,
and the existing normalized absolute value and valuation identities. No new
literature claim or representation hypothesis is introduced.
