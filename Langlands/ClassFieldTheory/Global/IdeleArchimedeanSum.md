# Canonical archimedean idele invariant sum

## Meaning and scope

For a finite Galois extension of number fields `E/F`,
`canonicalArchimedeanIdeleInvariantSum` is the additive homomorphism from
`relativeIdeleCohomology F E 2` to `RationalModIntegers` obtained by summing
`archimedeanIdeleInvariantAt v` over every infinite place `v` of `F`.
The summands are the actual idele cohomology invariants constructed from the
sign of a cocycle value at complex conjugation. The infinite places form a
finite type. The definition is noncomputable, since the summands use chosen
lifts whose independence was proved in `IdeleArchimedeanChoice`.

`canonicalArchimedeanIdeleInvariantSum_eq` identifies this map with
`archimedeanIdeleInvariantSum wi` for every family `wi` of upper places above
the base places. The equality is an equality of additive homomorphisms.

## Restriction

For a compatible tower of number fields `F → K → E`, with `E/F` Galois,
`canonicalArchimedeanIdeleInvariantSum_relativeIdeleRestriction` proves

```
canonicalArchimedeanIdeleInvariantSum (relativeIdeleRestriction F K E 2 x)
  = Module.finrank F K • canonicalArchimedeanIdeleInvariantSum x.
```

The intermediate extension `K/F` need not be normal. The upper extension
`E/K` is Galois by the tower theorem. The proof first groups the infinite
places of `K` by their restriction to `F`. The helper
`sum_infinitePlaces_eq_sum_placesOver` performs this reindexing for any
function into an additive commutative monoid, using `Finset.sum_fiberwise`.
The local restriction formula from `IdeleArchimedeanRestriction` then gives
`v.inertiaDeg w` times the invariant at `v` for each `w` above `v`. Summing
these degrees uses Mathlib's
`NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank`; distributing natural
scalar multiplication through the sum gives the displayed formula.

`archimedeanIdeleInvariantSum_relativeIdeleRestriction` gives the same formula
for any chosen-place sums on the two bases. No compatibility between the two
families of chosen places is needed.

## Inflation

For a compatible tower `F → E → L` of number fields with both `E/F` and `L/F`
Galois, `archimedeanIdeleInvariantAt_relativeIdeleInflation` proves preservation
of the invariant at each base infinite place. Choose an upper place of `L`,
restrict it to `E`, use the actual idele inflation formula from
`IdeleArchimedeanTower`, and identify both values with their canonical values.
Summing proves `canonicalArchimedeanIdeleInvariantSum_relativeIdeleInflation`.
The final theorem
`archimedeanIdeleInvariantSum_relativeIdeleInflation_of_arbitrary_choices`
transfers this to any two chosen-place sums, removing the chosen-place
compatibility hypothesis needed by the earlier direct tower formula.

## Provenance

This is internal derived infrastructure. Its mathematical inputs are the
existing actual archimedean idele invariants and their local tower laws,
Mathlib's finite-sum reindexing, and the infinite-place degree-sum theorem in
`Mathlib.NumberTheory.NumberField.Completion.Ramification`. It introduces no
new source claim or arithmetic hypothesis. It concerns only the archimedean
part of idele cohomology; it does not construct the invariant on idele-class
cohomology, prove finite-place laws, or prove `GlobalInvariantStatement`.
