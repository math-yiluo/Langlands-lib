# The base value group of a local field in `ℤ̂`: targets (M163.004, M163.006–M163.008, M163.010, M163.011, M163.013)

This module states seven NYLL source theorems as closed propositions. It
exports seven Prop-valued `def`s in the namespace
`Langlands.NYLL.LocalClassFieldTheory`:

- `baseFieldUnitsEquiv_valStatement` (M163.004);
- `localBaseValuation_baseFieldUnitsEquivStatement` (M163.006);
- `localBaseValuation_rangeStatement` (M163.007);
- `intToProCInteger_mem_localBaseValuation_rangeStatement` (M163.008);
- `localValueGroupReduction_surjectiveStatement` (M163.010);
- `localValueGroupReduction_kerStatement` (M163.011);
- `localCanonicalValueQuotientMap_bijectiveStatement` (M163.013).

Nothing is proved here. The proofs are separate units under the source theorem
names in the same namespace (the name without the suffix `Statement`).

## Setting

Let `K` be a nonarchimedean local field: a field `K : Type` with
`ValuativeRel`, `TopologicalSpace` and Mathlib's `IsNonarchimedeanLocalField`
instances. Let `K^sep = SeparableClosure K`, let `G = Gal(K^sep / K)`, and let
`A` be `Additive (K^sep)ˣ` with its Galois action. The
[definitions module](../U001/Definitions.md) (M163.001–M163.003, M163.005,
M163.009) supplies:

- `baseFieldUnitsEquiv K : Additive Kˣ ≃+ A^G`, where `A^G` is
  `ambientFixedAddSubgroup (intrinsicAbsoluteUnits K)
  (baseField (intrinsicAbsoluteGalois K))`, the elements of `A` fixed by the
  base subgroup `G`;
- `localBaseValuation K : A^G →+ ℤ̂`, which sends `baseFieldUnitsEquiv K x`
  to `v(x)` cast into the profinite integers `ℤ̂ = ZHat`;
- `localValueGroupReduction K n hn : (localBaseValuation K).range →+ ZMod n`,
  the inclusion into `ℤ̂` followed by `zHatReduction n hn`, reduction modulo
  a positive integer `n`.

Here `v(x) = valuationMap K x` is NYLL's integer valuation on `Additive Kˣ`.

**Sign convention.** NYLL's `valuationMap` is the *negative* of the usual
normalized discrete order `ord`, for which a prime element `π` of the
valuation ring `𝒪[K]` has `ord(π) = 1`: so `v(x) = -ord(x)`. It is built from
Mathlib's order-preserving isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` onto
`WithZero (Multiplicative ℤ)`, so elements of valuation less than one get
negative integers. The source proves that a prime element of `𝒪[K]` has
`v = -1` and its inverse has `v = 1` (`v_integerRingIrreducibleFieldUnit` and
`v_integerRingIrreducibleFieldUnit_inv`, original `IdealQuotients.lean`, lines
210–244). The published audit
`notes/reuse/nyll-finite-local-reciprocity-audit.md` (section 2.3) and the
published Markdown of the [definitions module](../U001/Definitions.md) record
the same convention. In M163.006 the value of `localBaseValuation K` at the
element corresponding to a prime element is therefore `-1`, not `1`. The other
targets concern only the range of `localBaseValuation K`, the image of `ℤ`
in `ℤ̂`. Negation maps that image onto itself, so the sign does not affect
them.

## The propositions

Each target quantifies the source section variables (lines 32–33) first,
with their kinds: `K` explicit and the instances instance-implicit. The
theorem's own binders follow. There are no level parameters: `K` lives in
`Type`, as in the source.

### `baseFieldUnitsEquiv_valStatement` (M163.004)

```lean
def baseFieldUnitsEquiv_valStatement : Prop :=
  ∀ (K : Type) [Field K] (x : Kˣ),
    ((Additive.toMul
      ((baseFieldUnitsEquiv K (Additive.ofMul x)).1 :
        Additive (SeparableClosure K)ˣ) : (SeparableClosure K)ˣ) :
      SeparableClosure K) = algebraMap K (SeparableClosure K) (x : K)
```

For a unit `x` of `K`, the fixed coefficient `baseFieldUnitsEquiv K x` is,
as an element of `K^sep`, the image `algebraMap K K^sep x`. The source theorem
carries `omit [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K] in` (line 49), so only `[Field K]` is
quantified; `baseFieldUnitsEquiv K` itself needs only `[Field K]`.

### `localBaseValuation_baseFieldUnitsEquivStatement` (M163.006)

```lean
def localBaseValuation_baseFieldUnitsEquivStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Additive Kˣ),
    localBaseValuation K (baseFieldUnitsEquiv K x) =
      Int.castRingHom ZHat
        (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x)
```

On the fixed coefficient of a unit `x`, the transported valuation is `v(x)`
cast into `ℤ̂`, with `v = -ord` as above.

### `localBaseValuation_rangeStatement` (M163.007)

```lean
def localBaseValuation_rangeStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    (localBaseValuation K).range =
      (Int.castRingHom ZHat).toAddMonoidHom.range
```

The value group, the range of `localBaseValuation K` as an additive subgroup
of `ℤ̂`, equals the image of `ℤ` in `ℤ̂`.

### `intToProCInteger_mem_localBaseValuation_rangeStatement` (M163.008)

```lean
def intToProCInteger_mem_localBaseValuation_rangeStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (m : ℤ),
    Int.castRingHom ZHat m ∈
      (localBaseValuation K).range
```

Every integer `m`, cast into `ℤ̂`, is a value. The source docstring says this
is required by the Henselian valuation condition.

### `localValueGroupReduction_surjectiveStatement` (M163.010)

```lean
def localValueGroupReduction_surjectiveStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (hn : 0 < n),
    Function.Surjective (localValueGroupReduction K n hn)
```

For every positive `n`, reduction modulo `n` maps the value group onto
`ZMod n`.

### `localValueGroupReduction_kerStatement` (M163.011)

```lean
def localValueGroupReduction_kerStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (hn : 0 < n),
    (localValueGroupReduction K n hn).ker =
      nsmulWithin (localBaseValuation K).range n
```

Write `Z` for the value group. For every positive `n`, the kernel of
reduction modulo `n` on `Z` is `nZ`, the subgroup `nsmulWithin Z n` of
elements `n • z` with `z ∈ Z`.

### `localCanonicalValueQuotientMap_bijectiveStatement` (M163.013)

```lean
def localCanonicalValueQuotientMap_bijectiveStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (hn : 0 < n),
    Function.Bijective
      (canonicalValueQuotientMap (localBaseValuation K).range n hn)
```

For every positive `n`, the canonical map `Z / nZ → ZMod n` is bijective.
That map is induced by the inclusion `Z ≤ ℤ̂` and reduction modulo `n`. This
is the map required by the valuation-quotient axiom; the source docstring
calls it the inclusion-and-reduction quotient map of the Henselian valuation
condition, here for the actual local value group.

## Published declarations used

- `baseFieldUnitsEquiv`, `localBaseValuation` and `localValueGroupReduction`
  (M163.003, M163.005, M163.009), from
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.HenselianValuationBase.U001.Definitions`
  ([Markdown](../U001/Definitions.md)). Their types use the published
  `intrinsicAbsoluteGalois K = Gal(SeparableClosure K / K)` and
  `intrinsicAbsoluteUnits K = galoisAmbientUnitsRep K (SeparableClosure K)`
  (M091.001, M091.002), which the published M163 definitions use in place of
  the source abbreviations M163.001 and M163.002.
- `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap`
  (M134.002,
  [definition](../../../../../../ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence/Definitions.md)),
  NYLL's integer valuation with the sign convention above.
- `Langlands.NYLL.ClassFormation.ZHat` (the profinite integers) and
  `Langlands.NYLL.ClassFormation.zHatReduction n hn`, the continuous additive
  reduction `ℤ̂ → ZMod n`, from
  [ProfiniteIntegerCore](../../../../../../GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore/Definitions.md);
  `localValueGroupReduction` is built from the latter.
- `Langlands.NYLL.ClassFormation.nsmulWithin` and
  `Langlands.NYLL.ClassFormation.canonicalValueQuotientMap` (M025), from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.Definitions`
  ([Markdown](../../../../../AbstractClassFieldTheory/Degree/Valuation/Definitions.md)).
  `nsmulWithin Z n` is the range of multiplication by `n` on `Z`.
  `canonicalValueQuotientMap Z n hn` is the map `Z / nsmulWithin Z n → ZMod n`
  lifted from `zHatReduction n hn` restricted to `Z`.
- `SeparableClosure`, `Int.castRingHom`, `AddMonoidHom.range`,
  `AddMonoidHom.ker`, `Function.Surjective` and `Function.Bijective` are
  Mathlib's.

## Imports and scope

The imports are
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.HenselianValuationBase.U001.Definitions`
(the M163 definitions, and through its imports `valuationMap`, `ZHat`,
`zHatReduction`, `SeparableClosure` and the Galois-module infrastructure) and
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.Definitions`
(for `nsmulWithin` and `canonicalValueQuotientMap`).

The remaining source unit M163.012, the definition
`localValueGroupQuotientEquivZMod`, is data whose body uses the proofs of
M163.010 and M163.011. It is left for a definition unit after those proofs
are published.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, readable in the project
snapshot under `n-yamaguchi-0729--ClassFieldTheory/source/`. The full file has
SHA-256 `1cd6d5fb117831219fac27dbb60cc7c3d7d866ad78fc4f771acdf694d3aa3ad9`,
the value recorded for M163 in the
[public declaration partition](../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m163).
The source opens namespace `LocalClassFieldTheory` (line 21), opens
`RamificationTheory`, `KummerTheory`, `LocalFieldTheory` and
`ClassFormation` (lines 22–26), works in `noncomputable section` (line 30)
and declares the section variables at lines 32–33.

| Partition unit | Original theorem in `LocalClassFieldTheory` | Original lines (docstring to type) | Adapted target in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- | --- | --- |
| M163.004 | `baseFieldUnitsEquiv_val` (`@[simp]`, with `omit`) | 49–56 | `baseFieldUnitsEquiv_valStatement` |
| M163.006 | `localBaseValuation_baseFieldUnitsEquiv` (`@[simp]`) | 73–78 | `localBaseValuation_baseFieldUnitsEquivStatement` |
| M163.007 | `localBaseValuation_range` | 81–85 | `localBaseValuation_rangeStatement` |
| M163.008 | `intToProCInteger_mem_localBaseValuation_range` | 97–100 | `intToProCInteger_mem_localBaseValuation_rangeStatement` |
| M163.010 | `localValueGroupReduction_surjective` | 110–112 | `localValueGroupReduction_surjectiveStatement` |
| M163.011 | `localValueGroupReduction_ker` | 121–124 | `localValueGroupReduction_kerStatement` |
| M163.013 | `localCanonicalValueQuotientMap_bijective` | 167–171 | `localCanonicalValueQuotientMap_bijectiveStatement` |

The partition rows assign the source theorem names, in the prefixed
namespace, to the adapted theorems; those names are reserved for the proofs.
No declaration of these names, and no equivalent target, exists in the
current Library or Mathlib. The Library's `notes/errata/` has no NYLL entry,
and the partition records no patch10 change to this file.

Worker 85 made these changes on 15 November 2026:

- added the `Langlands.NYLL` prefix to the namespace and kept the source
  `open` lines unchanged; inside the prefixed namespace they open the
  `Langlands.NYLL` namespaces of the same names;
- packaged each theorem type as a closed proposition, a `def` with the suffix
  `Statement`. The section variables become the leading `∀`-binders, with the
  same kinds, followed by the theorem's own binders. The type after the
  binders is the source type unchanged. For M163.004 the three instances
  omitted by the source `omit` line are not quantified;
- omitted the proofs, the `@[simp]` attributes of M163.004 and M163.006, the
  `noncomputable section` and all other declarations, and wrote new
  docstrings;
- replaced the source imports by the published modules above.

No draft from another worker was used.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), against Library
commit `fab9caeae532b7a65e67e702bcab72d3194371ae`, compiled this module with
no errors or warnings. Inspection reported each of
the seven declarations as a `definition` with no level parameters and
`statement_returns_prop: true`, using only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

A private probe, not part of this module, replays the source proofs of
M163.006, M163.007, M163.008, M163.010, M163.011 and M163.013 against these
closed targets after introducing the binders, with no errors. One step of the
M163.011 proof changes: the source rewrites with `zHatReduction_int`, but the
published `zHatReduction_int` has the closed target type
`zHatReduction_intStatement n hn m`, which `rw` does not unfold. The probe
uses that theorem as the equation `zHatReduction n hn m = (m : ZMod n)`
instead. For M163.004, the probe reduces the target by `change` to the
published M096.002 target `baseUnitsEquivGaloisAmbientFixed_valStatement`,
as the source proof does. That proof is not yet in the Library. These
development checks are not independent acceptance.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The Lean file keeps the original copyright and author header verbatim
(copyright 2026 Naganori Yamaguchi; authors Naganori Yamaguchi, assisted by
OpenAI Codex) and records the modifications. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are unchanged in the
Library, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
