# Residue characteristic of a chosen local-field package

This module extracts exactly two source units, M334.009 (lines 78–80) and
M334.012 (lines 95–98), of Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean#L78-L98)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The source file's SHA-256 is
`69d3219d17ef6bef4204e02538d5a3f28ee63edb1bc1e0be2354bed4c739afe9`.
Its header, imports, universe and namespace context, the two selected
declarations and the intervening lines 82–93 were read directly.

The original is available in the registered source
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), under
`n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The recorded patch10 does not change this source module.

## Declarations

All names below are relative to
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`. Both declarations
have implicit `{K : Type u} [Field K]` and explicit
`(F : LocalField.{u, v} K)`, where `LocalField` is the published shared
package of the module
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`.
The field universe `u` and the value-group universe `v` are independent.

### `LocalField.residueCharacteristic` (M334.009)

```lean
noncomputable abbrev residueCharacteristic (F : LocalField.{u, v} K) : ℕ :=
  ringChar F.residueField
```

The residue characteristic is Mathlib's `ringChar` of the published residue
field `F.residueField`, which is reducibly the residue field
`IsLocalRing.ResidueField` of the valuation subring of the chosen valuation
(through the published `CompleteDVF` projections). `ringChar R` is the unique
natural number `p` with `CharP R p`, so `F.residueCharacteristic` is the
characteristic of the residue field: `0` if the residue field had
characteristic zero, and otherwise the positive generator of the kernel of
`ℕ → F.residueField`. The definition itself does not assert primality or
nonvanishing; primality is the separate statement target
`LocalField.residueCharacteristic_primeStatement` of the module
`Basic.ResidueCharacteristicPrimeStatement`. The abbreviation is reducible,
as in the source, so it unfolds to `ringChar F.residueField` during
instance search and unification.

### `LocalField.residueField_charP_residueCharacteristic` (M334.012)

```lean
instance residueField_charP_residueCharacteristic (F : LocalField.{u, v} K) :
    CharP F.residueField F.residueCharacteristic :=
  ringChar.charP (R := F.residueField)
```

This registers, as a global instance with default priority, the fact that the
residue field has characteristic `F.residueCharacteristic`. Its body is
Mathlib's `ringChar.charP` at `R := F.residueField`, exactly as in the source.

Instance analysis. `CharP R p` is a `Prop`-valued class, so any two instances
of the same `CharP` type are definitionally equal by proof irrelevance; the
instance introduces no data and no diamond. Mathlib already declares
`ringChar.charP : CharP R (ringChar R)` as a low-priority instance, and this
source instance is a default-priority specialisation of it to the residue
field of a local-field package, stated with the named characteristic
`F.residueCharacteristic`. It therefore does not compete with any
data-carrying instance and changes no definitional behaviour; it only makes
the source interface `CharP F.residueField F.residueCharacteristic` directly
available, as in the original. No other instance is introduced.

## Exact source correspondence

Write `S = LocalFieldTheory.DiscreteValuationField` for the original
namespace and `T = Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`
for the adapted namespace.

| Source unit and declaration | Source lines | Adapted declaration | Type and body |
| --- | --- | --- | --- |
| M334.009, `S.LocalField.residueCharacteristic` | 78–80 | `T.LocalField.residueCharacteristic` | `noncomputable abbrev`, type `ℕ`, body `ringChar F.residueField`. |
| M334.012, `S.LocalField.residueField_charP_residueCharacteristic` | 95–98 | `T.LocalField.residueField_charP_residueCharacteristic` | `instance`, type `CharP F.residueField F.residueCharacteristic`, body `ringChar.charP (R := F.residueField)`. |

The declaration kinds (`noncomputable abbrev`, `instance`), binder kinds and
order, types, bodies and docstrings are those of the source. The source
`variable {K : Type u} [Field K]` (line 42) and the `LocalField` namespace
(line 40) are retained.

## Import and scope

The imports are exactly:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`,
  the published module supplying `LocalField`, its finite-residue-field
  instance and the residue-data abbreviations (M334.001–005);
- `Mathlib.Algebra.CharP.Defs`, which supplies `ringChar`, `CharP` and
  `ringChar.charP`.

They replace the nine upstream imports of the source file. Only the two
listed source units are extracted. The intervening theorems
`residueCharacteristic_ne_zero` (M334.010, lines 82–85) and
`residueCharacteristic_prime` (M334.011, lines 87–93) are not declared here;
the prime target of M334.011 is in the sibling module
`Basic.ResidueCharacteristicPrimeStatement`. The `Fact` instance M334.013,
which uses the proof of M334.011, and all later source declarations are
outside this module.

## Attribution and complete modification record

The original 2026 copyright, Apache-2.0 release line and author header are
retained verbatim. The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused. Their SHA-256
values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

Worker 125 made these modifications on 13 November 2026:

- extracted M334.009 and M334.012 with their declaration docstrings into this
  focused module, omitting all other source declarations;
- prefixed both the declaration namespace and the opened valuation namespace
  with `Langlands.NYLL`;
- replaced the nine upstream imports by the two imports above;
- removed the unused universe variables `w x`, retaining independent `u v`;
- replaced the module documentation, added the prominent modification
  notice in the Lean header, and wrote this paired Markdown.

No declaration body, mathematical type, binder, instance attribute or
priority is changed beyond qualification of names to the published namespace.
