# Degree-two relative corestriction after restriction

Author: Worker 279.

`RelativeH2CorestrictionRestrictionStatement` states that for every tower
of fields `K → L → M` in which `M` is finite Galois over both `K` and `L`,
and for every class `x` in `H²(Gal(M/K), Mˣ)`,

```
Cor_{M/L → M/K}(Res_{M/K → M/L}(x)) = [L : K] · x.
```

## Exact Lean content

The proposition quantifies:

- three fields `K L M` in one arbitrary common universe `u`;
- algebra structures `K → L`, `K → M` and `L → M`, with `IsScalarTower K L M`
  expressing that the specified embeddings are compatible;
- `FiniteDimensional K L`, `FiniteDimensional K M` and `FiniteDimensional L M`;
- `IsGalois K M` and `IsGalois L M`;
- every `x : relativeCohomology K M 2`.

It asserts

```
relativeCorestriction K L M 2 (relativeRestriction K L M 2 x) =
  Module.finrank K L • x
```

with natural-number scalar multiplication in the additive group
`relativeCohomology K M 2`.

`L/K` is not assumed to be normal or Galois, so `L` may be any intermediate
field of a finite Galois extension `M/K`. The hypotheses `FiniteDimensional L M`
and `IsGalois L M` follow from the others; they are listed explicitly as the
task specifies. No characteristic, valuation or local-field hypothesis
appears. The common universe matches `relativeRestriction`, which requires
all three fields in one universe. `relativeCorestriction` permits
independent universes, and here it is applied in that common universe.

## The maps and groups

All three objects are imported unchanged from the Library:

- `relativeCohomology K M 2`, from `Langlands.ClassFieldTheory.Local.Cohomology`,
  is Mathlib's ordinary group cohomology of the finite group `Gal(M/K)`
  acting on `Additive Mˣ`, over `IntegerScalars = ULift ℤ`.
- `relativeRestriction K L M 2`, from the same module, is the morphism
  induced by the restriction-of-scalars homomorphism `Gal(M/L) → Gal(M/K)`
  together with the identity on `Mˣ`.
- `relativeCorestriction K L M 2`, from
  `Langlands.ClassFieldTheory.Local.Corestriction`, reindexes `Gal(M/L)`
  cohomology to the actual subgroup `relativeGaloisSubgroup K L M` of
  `Gal(M/K)`, passes to Tate cohomology by Mathlib's positive-degree
  comparison, applies the published Tate corestriction, and returns to
  ordinary cohomology.

No substitute map, comparison law or hypothesis relating these maps is
introduced.

## Original source

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
GTM 67, Springer, 1979. Registered source `serre-1979-local-fields`,
SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Worker 279 read the passages below in that file.

- Chapter VII, section 7, Proposition 6, printed page 119 / PDF page 125:
  for a subgroup `H` of finite index `n` in `G`, `Cor ∘ Res = n` on
  `H^q(G, A)`. The statement here is the case `q = 2`, with
  `G = Gal(M/K)`, `H` the subgroup fixing `L`, and `A = Mˣ`.
- Chapter XI, section 2, printed page 168 / PDF page 174: the proof of the
  corestriction compatibility of invariants applies this proposition in
  degree two, giving `inv_E ∘ Cor ∘ Res = [E' : E] · inv_E`. Section 3 on
  the same page lists `Cor(u_{F/E'}) = [E' : E] · u_{F/E}`, the formula
  this identity is used to derive downstream.

In Serre, `n` is the index of `H` in `G`. This statement writes the
multiplier as `Module.finrank K L`. For finite Galois `M/K` and the actual
subgroup `relativeGaloisSubgroup K L M`, the index equals `[L : K]` by the
fundamental theorem of Galois theory. That identification is part of the
eventual proof; it is not assumed or asserted in this statement.

## Provenance and scope

This is a derived prerequisite target. A downstream argument derives the
fundamental-class corestriction law from the restriction law and this
identity, without assuming corestriction compatibility as a hypothesis.
The generic Tate identity `Langlands.Tate.corestriction_restriction`, with
multiplier `H.index` in every degree, is published in
`Langlands.Cohomology.Tate.TransferProof`. A proof of this statement must
compare `relativeRestriction` with the Tate restriction through
`relativeSubgroupCohomologyIso` and the ordinary/Tate comparison, then
identify the index with `Module.finrank K L`.

This file only defines the proposition. It does not prove it, and it says
nothing about other degrees, injectivity, or the converse composite
`Res ∘ Cor`.
