# Proof of permutation invariance of irreducible complex principal series

Module `Langlands.Representation.Archimedean.ComplexStandardPermutationProof`.

## Statement

`Langlands.Archimedean.complexStandardPermutation : ComplexStandardPermutationStatement`. The
target is stated in `ComplexStandardSurjectionInjectiveReduction` and left unchanged. For every
`n` and all lists `ds`, `es` of complex characters with `ds.length = n` and `es.Perm ds`: if
the `U(n)`-finite functions `X(ds)` of the standard module of `ds` form an irreducible
`(𝔤𝔩_n(ℂ), U(n))`-module, there is a bijective linear map `T : X(es) → X(ds)` with
`IsComplexStandardIntertwining n (complexStandardRep n ds) (complexStandardLie n ds) es T`.

## Proof

The theorem is the composite of three results:

```
complexStandardPermutation :=
  ComplexPermutation.complexStandardPermutation_of_swapJacquet
    (ComplexSwapJacquet.swapJacquet_of_nonvanishing
      ComplexSwapJacquet.exists_integral_integrand_ne_zero)
    complexJacquetFrobenius
```

1. **Reduction to one rank-one Jacquet functional** (`ComplexPermutationReduction` and the
   modules it imports: `ComplexPermutationEndomorphism`, `ComplexPermutationKType`,
   `ComplexPermutationKMap`, `ComplexPermutationSwap`). A permutation is a product of adjacent
   transpositions, and irreducibility passes along bijective intertwining maps. So it suffices
   to treat `ds = pre ++ d :: e :: post` and `es = pre ++ e :: d :: post`. Suppose
   `Re t_d ≥ Re t_e` (otherwise exchange the roles) and `(l_d, t_d) ≠ (l_e, t_e)` (otherwise
   `es = ds`). Then `SwapJacquetStatement` provides a nonzero Jacquet functional on `X(ds)` with
   the exponents of `es`. Frobenius reciprocity turns it into a nonzero intertwining map
   `X(ds) → X(es)`, which is injective because `X(ds)` is irreducible. It is surjective because
   every `U(n)`-type has the same finite multiplicity in `X(ds)` and in `X(es)`: there are
   injective `U(n)`-maps in both directions, built from the Frobenius function of
   `ComplexJacquetFrobeniusFunction`, and an invariant inner product splits finite-dimensional
   `U(n)`-subspaces. Its inverse is the required `T`.
2. **Frobenius reciprocity** `complexJacquetFrobenius` (Library,
   `ComplexJacquetFrobeniusProof`), used at universe `0`.
3. **The rank-one Jacquet functional.** At the positions `i = pre.length`, `j = i + 1` let
   `C(z) = s x(z)`, with `s` the permutation matrix of `(i j)` and `x(z) = 1 + z E_ij`. The
   functional is `Λ_c(f) = ∫_ℂ (R(c E_jj) f - κ_j(c) f)(C(z)) dz`.
   * `ComplexSwapJacquetLie`: the pointwise identities for right derivatives of `f` along
     `C(z)` and at `1`.
   * `ComplexSwapJacquetAnalysis` and `ComplexSwapJacquetDecay`: integration by parts on `ℂ`
     and decay of the integrand.
   * `ComplexSwapJacquetFunctional`: `Λ_c` is a well-defined Jacquet functional with the
     exponents of `es`.
   * `ComplexSwapJacquetProof`: `swapJacquet_of_nonvanishing` derives `SwapJacquetStatement`
     from any nonvanishing input.
   * `ComplexSwapJacquetNonvanishing`: `exists_integral_integrand_ne_zero` supplies a
     `U(n)`-finite vector with `Λ_c(F) ≠ 0`, taking `c = 1` or `c = i`.

Each module's Markdown explains its part in detail.

`ComplexStandardSurjectionInjectiveReduction.md` explains how the statement follows from
Knapp 1986 (Proposition 10.18, Theorem 10.6, Corollary 10.42) after restriction to `SL_n(ℂ)`.
The proof implemented here takes a different, direct route on `GL_n(ℂ)`, without global
characters or restriction to `SL_n(ℂ)`. The rank-one intertwining operator of a simple
reflection enters only through its Jacquet functional (its value at `1`), and the multiplicity
count above replaces character theory. In `Λ_c`, the function is replaced by
`R(c E_jj) f - κ_j(c) f`, which vanishes at `1`. This makes the integral converge absolutely
for `Re t_d ≥ Re t_e`, including the line `Re t_d = Re t_e`, so analytic continuation is not
used.

## Authors

Worker 28 wrote the permutation reduction, `ComplexSwapJacquetLie`,
`ComplexSwapJacquetNonvanishing` and this module. Worker 48 wrote `ComplexSwapJacquetChart`,
`ComplexSwapJacquetAnalysis`, `ComplexSwapJacquetDecay`, `ComplexSwapJacquetFunctional` and
`ComplexSwapJacquetProof`.
