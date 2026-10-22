# Restriction and corestriction on relative Tate cohomology

Author: Worker 42.

For a tower of fields `K → L → M`, the published
`relativeGaloisSubgroup K L M` is the actual image of
`Gal(M/L) → Gal(M/K)` under restriction of scalars. Its published group
equivalence with `Gal(M/L)` changes only the base field of each
automorphism.

`relativeSubgroupUnitsIso` identifies the actual unit representations
along this group equivalence. Its linear map is the identity on
`Additive Mˣ`; equivariance follows by applying the inverse law of the
group equivalence to each unit. `integralSubgroupCoefficientsIso` is
the identity on the actual lifted integers with their trivial actions.

When `M/K` and `M/L` are finite dimensional, `relativeSubgroupTateIso`
and `integralSubgroupTateIso` apply the constructed chain-level Tate
reindexing to these coefficient isomorphisms, in every integer degree.
Thus the comparisons concern Mathlib's actual Tate cohomology, including
the norm splice in degrees minus one and zero. They are constructed
isomorphisms, not additional hypotheses.

For each integer `n`, the four maps have the following directions:

| Map | Source | Target |
| --- | --- | --- |
| `relativeTateRestriction` | `Ĥⁿ(Gal(M/K), Mˣ)` | `Ĥⁿ(Gal(M/L), Mˣ)` |
| `relativeTateCorestriction` | `Ĥⁿ(Gal(M/L), Mˣ)` | `Ĥⁿ(Gal(M/K), Mˣ)` |
| `integralTateRestriction` | `Ĥⁿ(Gal(M/K), ℤ)` | `Ĥⁿ(Gal(M/L), ℤ)` |
| `integralTateCorestriction` | `Ĥⁿ(Gal(M/L), ℤ)` | `Ĥⁿ(Gal(M/K), ℤ)` |

Restriction applies the constructed subgroup restriction and then the
inverse reindexing. Corestriction first reindexes to the subgroup and
then applies the constructed subgroup corestriction. All finite
enumerations are supplied by `Fintype.ofFinite`, as in the existing local
Tate groups. The scalar ring in all four maps is `IntegerScalars.{u}`,
the lifted integer ring in the universe of `M`. The three field universes
are independent. No Galoisness or normality of the field extensions is
required for these constructions on their finite automorphism groups.

This is derived construction content: it specializes the published
finite-group transfer maps and chain-level reindexing to the actual
Galois subgroup and its unit or integral coefficients. Serre,
*Local Fields* (1979), XI.1, printed pp. 165–166 (PDF pp. 171–172),
defines the corresponding formation maps and extends restriction and
corestriction to every integer Tate degree. The generic construction
follows VIII.1–2, printed pp. 127–130 (PDF pp. 133–136).

`relativeSubgroupTateIso_positive` proves that the new reindexing agrees
with the existing `relativeSubgroupCohomologyIso` after the positive
Tate-to-ordinary comparisons. It specializes the generic reindexing
comparison; the coefficient maps are identical, so their proofs of
equivariance do not affect the resulting map.
`relativeTateCorestriction_positive` then applies subgroup corestriction
and the target comparison to this equality. It proves the commuting
diagram between `relativeTateCorestriction` and the previously published
`relativeCorestriction` in every positive degree.

These definitions do not prove cup compatibility, transitivity, the
subgroup-index formula, or agreement of Tate restriction with ordinary
cochain restriction. The ordinary corestriction comparison above concerns
the already published transport construction, not an independent cochain
transfer. Local fundamental classes and the associated cup diagrams are
separate statement obligations.

Source ID: `serre-1979-local-fields`. Retained PDF SHA256:
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
