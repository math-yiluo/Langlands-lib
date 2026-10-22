# Positive-degree relative Galois corestriction

Author: Worker 42.

## Actual finite subgroup and cohomology maps

For a field tower `K → L → M`, `relativeGaloisSubgroup K L M` is the image
of the injective restriction-of-scalars homomorphism
`Gal(M/L) → Gal(M/K)`. Its equivalence with `Gal(M/L)` is constructed by
`MonoidHom.ofInjective`. The displayed application certificate proves that
the resulting ambient automorphism is exactly the same automorphism with
scalars restricted to `K`.

`relativeSubgroupCohomologyIso K L M n` identifies ordinary cohomology of
`Gal(M/L)` acting on `Additive Mˣ` with ordinary cohomology of this subgroup
acting on the restriction of `unitsRepresentation K M`. It uses Mathlib's
`groupCohomology.mapIso`, the constructed group equivalence, and the
identity linear equivalence on the actual coefficient group. Equivariance
is definitional. No cohomology comparison or inverse is supplied as data.

Assuming `M/K` is finite dimensional, `relativeCorestriction K L M n`
is a linear map

```
Hⁿ(Gal(M/L), Additive Mˣ) → Hⁿ(Gal(M/K), Additive Mˣ),
```

for every positive natural number `n`. The positivity condition is the
typeclass `NeZero n`. The construction first reindexes to the actual
subgroup, passes to Tate cohomology by the inverse of Mathlib's
positive-degree comparison, applies the published all-degree Tate
corestriction, and returns to ordinary cohomology by the positive-degree
comparison. `relativeCorestriction_eq` records this exact composite by
definitional equality.

The scalar ring is `IntegerScalars = ULift ℤ` in the universe of `M`.
All three field universes are independent. Only the ambient finite-dimensional
hypothesis is needed for the map; the group and subgroup enumerations
are supplied by `Fintype.ofFinite`. Galoisness and normality of `L/K` are
not needed to construct it.

This defines ordinary corestriction by transport of the published Tate
construction. It does not compare it with a separately defined cochain
transfer, nor prove transitivity, a restriction-corestriction formula, or
independence of alternative finite enumerations.

## Predicate on a local invariant family

`InvariantFamily.RelativeCorestriction I` asserts

```
inv(M/F)(Cor(M/E → M/F)(c)) = inv(M/E)(c).
```

It quantifies all primes (through the parameter `p` and `Fact p.Prime`),
all towers of `p`-adic fields `F → E`, and all finite extensions `M`
Galois over both fields. The two base fields share an arbitrary universe,
and `M` lies in an independent arbitrary universe. The scalar-tower
hypotheses refer to the actual specified embeddings. `E/F` is not
required to be Galois.

This is a predicate on raw invariant data. It neither asserts that an
invariant family exists nor assumes a family satisfying the desired laws
as part of an existence statement. No absolute continuous corestriction
is constructed here. A simultaneous local realization target and the
fundamental-class corestriction formula remain separate.

## Original source and provenance

Serre, *Local Fields* (1979), Chapter XI, section 2, Proposition 1(ii),
printed pp.167–168 / PDF pp.173–174, gives invariant compatibility with
corestriction. Its proof already works at a finite Galois upper extension:
restriction is surjective at that stage and corestriction composed with
restriction multiplies by the lower extension degree. The finite
invariant predicate records that compatibility on relative classes, with
the two relative invariants expressed as components of one raw family.
The injectivity conclusion of the source proposition is not asserted here.

The construction is derived implementation content: the actual finite
Galois subgroup identification is followed by Mathlib's ordinary/Tate
comparison and the published dimension-shifting corestriction from
`Langlands.Cohomology.Tate.TransferDefinitions`. It does not introduce
replacement coefficient groups or cohomology.

Registered original: `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 42 read the cited original pages directly.
