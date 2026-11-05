# Left multiplication by an integer power of a unit norm

The sole new declaration is
`Langlands.NYLL.LocalFieldTheory.normClass_normUnits_zpow_mul.{u}`.
Its unapplied type is exactly the independently published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassNormUnitsZpowMulStatement.{u}`.
The theorem has no external term or instance parameters. Its sole direct
import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U034.Statements`;
that statement's Lean/Markdown pair and complete imported chain are unchanged.

## Target and mathematical meaning

The closed proposition unfolds to

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (z : Lˣ) (n : Int) (x : Kˣ),
  normClass K L ((normUnits K L z) ^ n * x) = normClass K L x
```

All eight binders remain internal, with their source order and binder kinds:

| Position | Binder | Kind and role |
| --- | --- | --- |
| 1 | `K : Type u` | Explicit base-field type |
| 2 | `L : Type u` | Explicit extension-field type |
| 3 | `[Field K]` | Instance-implicit field structure on `K` |
| 4 | `[Field L]` | Instance-implicit field structure on `L` |
| 5 | `[Algebra K L]` | Instance-implicit algebra structure |
| 6 | `(z : Lˣ)` | Explicit extension-field unit |
| 7 | `(n : Int)` | Explicit integer exponent |
| 8 | `(x : Kˣ)` | Explicit base-field unit |

The single shared universe `u` is arbitrary. There is no finite-dimensionality,
finite-module, local-field, separability, Galois, valuation or topology premise.
The exponent remains an integer, including negative exponents interpreted by
inversion in `Kˣ`, and zero whose power is `1`. The power multiplies `x` on
the left in `Kˣ`, before the product is projected to the norm quotient.

All norm constructions are inherited public declarations in
`Langlands.NYLL.LocalFieldTheory`:

| Declaration | Actual meaning |
| --- | --- |
| `normUnits K L` | `Units.map (Algebra.norm K) : Lˣ →* Kˣ` |
| `localNormSubgroup K L` | `(normUnits K L).range` |
| `NormQuotient K L` | `Kˣ ⧸ localNormSubgroup K L` |
| `normClass K L` | The canonical homomorphism `QuotientGroup.mk' (localNormSubgroup K L)` |

The unit norm is defined in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`.
Under `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField`,
the subgroup, quotient, group structure and projection are in
`NormQuotient.U001.Definitions`, `NormQuotient.U002.Definitions`,
`NormQuotient.U003.Definitions` and `NormQuotient.U005.Definitions`,
respectively.
They are reused unchanged. Mathematically, an integer power of a norm has
trivial quotient class, so multiplying a representative by this power leaves
its class unchanged. This generic support interface does not substitute the
finite-dimensional host norm quotient for the source's general construction.

## Implemented proof

The proof first introduces the eight internal binders:

```lean
intro K L _ _ _ z n x
```

The three anonymous introductions install the two field structures and the
algebra structure as local instances. Lean unfolds the published proposition
to expose its quantifiers; no statement is changed. The remaining proof is
the pinned original route:

```lean
rw [map_mul, normClass_normUnits_zpow_eq_one K L z n]
exact one_mul (normClass K L x)
```

`map_mul` expands the projected product into the product of the two quotient
classes. The inherited public theorem
`normClass_normUnits_zpow_eq_one K L z n`, from U030.Proofs through the
unchanged U034 statement chain, identifies the first class with `1` for
every integer `n`. The goal becomes
`1 * normClass K L x = normClass K L x`, discharged by `one_mul`.
No sign split or restriction to natural exponents is introduced. The module
adds no instance or simp registration.

## Source pin and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:302–308`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L302-L308).
The docstring is at 302, the theorem and type binders at 303, field/algebra
structures and `z n x` at 304, the conclusion at 305–306, and the proof
at 307–308. The whole-file SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The source subgroup, quotient, commutative group and projection are at
26–54; the integer-power identity is at 268–272.

The original
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean` defines the actual
unit norm at 32–34. Its whole-file SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.
Worker 1560 read both complete retained originals on 5 November 2026 UTC.
The [public partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093)
places M093.034 after M093.033. No patch10 compatibility edit applies to M093.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Asserted type of `normClass_normUnits_zpow_mul` | Existing closed `NormClassNormUnitsZpowMulStatement.{u}` in U034.Statements |
| Proof `normClass_normUnits_zpow_mul` | Exact theorem `normClass_normUnits_zpow_mul.{u}` in this module |
| `normClass_normUnits_zpow_eq_one` | Existing U030.Proofs theorem, reused through the published chain |
| `normUnits`, `localNormSubgroup`, `NormQuotient`, `normQuotientCommGroup`, `normClass` | Existing public constructions with their original meanings, unchanged |
| `map_mul`, `one_mul` | Existing generic multiplicativity and left-identity results |

The adaptation adds the namespace prefix and uses the published closed
proposition as the theorem's entire type. Its eight introductions precede
the original proof body. The sole U034.Statements import replaces the
original import list. The original docstring is retained; the unused
universe `v`, noncomputable section and unrelated declarations are omitted.
Worker 1560 authored this proof extraction and companion directly from the
pinned original, without reusing an unpublished project draft or patch10
edits. There are no project coauthors for this pair.

The original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Both source-ID errata paths were checked under `notes/errata/` in the
workspace, project and supplied Library on 5 November 2026 UTC; all six
paths were absent.

## License, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by a dated modification record.
The inherited [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE), including applicable
dependency attribution, remain unchanged in `repository_paths`. Their
respective SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching the pinned originals.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Compilation is development
evidence; acceptance requires the Lake/kernel/exact-target checks,
unchanged statement and frozen dependencies, independent semantic review
and Integrator publication under `lean.proof@1`.

This module proves only M093.034. M093.035 onward and host adapters remain
separate work. Parent task `1cbd1968-d285-4b34-822c-f6b5599d1c38` retains
the named Artin family, actual norm kernel, surjectivity, host quotient
evaluation and bijectivity, actual quotient topology, finite discrete
Galois topology and both continuity directions for every prime and arbitrary
supplied `TF` and `TE`. Type 0 remains an intermediate host stage.
Normalization, inertia, universe transport and comparison with the
cohomological route require separate results; existing cohomological
definitions and frozen targets retain their meanings.
