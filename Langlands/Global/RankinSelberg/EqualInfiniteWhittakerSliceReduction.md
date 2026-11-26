# Equal-rank factorization from local Whittaker comparisons and tests

`equalInfiniteWhittakerSliceReduction` proves
`EqualInfiniteWhittakerSliceReductionStatement.{u,uQ}`. The conclusion
is exactly the Library's `EqualArchimedeanFactorizationStatement.{u,uQ}`.
The number-field and finite-presentation universes remain free. The
reduction includes `GL₁` and the empty finite set `S`.

The premises are the following.

- `InfiniteWhittakerSliceModelStatement` supplies `ModelData` for one
  actual cuspidal realization with its supplied spectral presentation,
  irreducible admissible finite components, a standard adelic character,
  and its real and complex parameters. At each infinite place, the one
  local model map has a nonzero identity evaluation and contains all
  corresponding actual single-place slices in its line. The slice
  equation allows arbitrary fixed vectors and group elements at the
  other infinite places and an arbitrary fixed finite tensor.
- `RealEqualPlaceTestsStatement` supplies actual opposite-character
  restrictions, quotient measure and Schwartz data at each real place.
  Each of the two local integrals for that data is holomorphic on a right
  half-plane and nonzero at a point of that half-plane.
- `ComplexEqualPlaceTestsStatement` supplies the same local data and
  holomorphic nonvanishing at a complex place.

`InfiniteWhittakerSliceModelAt F` expresses the single-representation comparison for all
supplied presentations over one field `F`. `equalInfiniteWhittakerTestAt_of_local` uses
that comparison to assemble the tests at `F`. Its real test premise applies when the
real-place subtype of `F` is nonempty.

Apply the single-representation comparison to the first realization
with the given unitary character and to the second with the inverse
character. Choose the local test data independently. The identity
theorem provides a nonzero value of each whole archimedean product on
every right half-plane.

For each of the two realizations, `exists_model_real` and
`exists_model_complex` lift the chosen local test functions to vectors
of the corresponding source models. Combine them in one actual
infinite pure tensor. `exists_normalized_product` factors its residual
with a common nonzero scalar after the finite reference tuple is fixed.
The single normalized residual nonvanishing result, proved by removing
unramified coordinates, supplies nonzeroness of this scalar. Multiplying
the first and second identities gives the ordinary joint residual
product required by `EqualInfiniteWhittakerTestStatement`, with the
product of the two scalars. The same selected test data carry the dual
nonvanishing.

The published `equalInfiniteWhittakerReduction` then constructs and
integrates the ordinary and dual products, retaining one scalar for
both, and constructs the Schwartz and Fourier products with scalar
one. This is an internal derivation from the Library's exact
factorization reduction, actual spectral tensor construction, finite
separation and measure results. The three stated archimedean premises
remain open.
