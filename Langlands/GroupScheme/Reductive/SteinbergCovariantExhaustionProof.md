# Unconditional covariant exhaustion by Steinberg-type products

Author: Worker 165. Worker 3483 supplied the composite term in Task 5311's context.

`Langlands.GroupScheme.steinbergCovariantExhaustion` has exactly the type
`Langlands.GroupScheme.SteinbergCovariantExhaustionStatement.{u}`, defined in
`Langlands.GroupScheme.Reductive.SteinbergCovariantExhaustionStatement`, for arbitrary
universe `u`. It proves the existence of the specified covariant-exhaustion data for
every simply connected group over an algebraically closed field of prime
characteristic, with the target's existing affine-structure instance. The theorem
adds no hypotheses.

The proof uses exactly these published theorems:

- `Langlands.GroupScheme.steinbergCovariantExhaustion_of_bigCell`
  in `Langlands.GroupScheme.Reductive.SteinbergBigCellReduction`;
- `Langlands.GroupScheme.steinbergBigCell_of_rootAndCoroot`
  in `Langlands.GroupScheme.Reductive.SteinbergBigCellRootCorootAssembly`;
- `Langlands.GroupScheme.rootDatumExistence`
  in `Langlands.GroupScheme.Reductive.RootDatumExistence`;
- `Langlands.GroupScheme.splitSimplyConnectedCorootSpan`
  in `Langlands.GroupScheme.SimplyConnected.SplitNecessity`.

The last two theorems discharge the two structural inputs of the big-cell assembly.
The resulting closed proof of `SteinbergBigCellStatement.{u}` is supplied directly to
the covariant-exhaustion reduction. That published reduction provides the actual
subgroup maps and weights, the injective difference comorphism, the unit-product
condition, exhaustion of invariant coordinates and cofinal irreducibility with
equal-size bases. All quantifiers over test schemes and all universe parameters are
those of the existing target.

This is an internal composition of published proofs. The target's Markdown explains
its reconstruction from the Haboush proof sketch and the precise scope of the
interface. This module preserves that statement and its imports.
