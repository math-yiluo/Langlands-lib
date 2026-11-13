# Primality of the residue characteristic: statement target (M334.011)

This module defines one closed proposition target in
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`:
`residueCharacteristic_primeStatement.{u, v} : Prop`. It is the type of
the source theorem `residueCharacteristic_prime` (unit M334.011), with the
complete source telescope universally quantified inside the proposition in
its original order and with its original implicit, instance and explicit
binder kinds. Universe parameters `u v` are arbitrary and retain the
source order. This file supplies the statement only; its proof is a
separate `lean.proof@1` task, whose theorem keeps the source name
`residueCharacteristic_prime`.

## Complete proposition

```lean
def residueCharacteristic_primeStatement.{u, v} : Prop :=
  ∀ {K : Type u} [Field K] (F : LocalField.{u, v} K),
    Nat.Prime F.residueCharacteristic
```

For every field `K` in universe `u` and every local-field package
`F : LocalField.{u, v} K` (the published shared structure: a chosen complete
discrete valuation on `K` with value group in universe `v` and a finite
residue field), the residue characteristic
`F.residueCharacteristic = ringChar F.residueField` is a prime natural
number (`Nat.Prime`). The field universe `u` and the value-group universe `v`
are independent. `LocalField` and `residueField` are the published
declarations of
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`;
`residueCharacteristic` is the abbreviation (M334.009) of the sibling
module `Basic.ResidueCharacteristic`, submitted together with this target.
No hypothesis is
added and the conclusion is unchanged.

Mathematically the statement holds because the residue field is a finite
field: a finite ring has nonzero characteristic, and a nonzero
characteristic of a ring without zero divisors is prime. The finiteness of
the residue field is part of the `LocalField` package (its `residueFinite`
field, registered as an instance), not an extra hypothesis of the target.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean#L87-L93).
The original file SHA-256 is
`69d3219d17ef6bef4204e02538d5a3f28ee63edb1bc1e0be2354bed4c739afe9`.
The readable original is retained under the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The recorded patch10 does not change this source module.

| Unit | Original name | Source lines | Adapted target |
| --- | --- | --- | --- |
| M334.011 | `LocalFieldTheory.DiscreteValuationField.LocalField.residueCharacteristic_prime` | docstring 87, type 88–89, proof 90–93 | `residueCharacteristic_primeStatement` |

The source declaration is

```lean
theorem residueCharacteristic_prime (F : LocalField.{u, v} K) :
    Nat.Prime F.residueCharacteristic
```

under the section variables `{K : Type u} [Field K]` (line 42) in namespace
`LocalFieldTheory.DiscreteValuationField.LocalField`. The target quantifies
these section variables first, then the explicit `F`, exactly as the source
theorem's elaborated type.

## Adaptation and reuse

Worker 125 extracted the source theorem type, prefixed the namespace with
`Langlands.NYLL`, suffixed the name with `Statement`, and moved the complete
source telescope (including the section variables) into the proposition
body. The formula, binder kinds and order are unchanged. The source proof
(lines 90–93) is omitted. Explicit universe parameters `.{u, v}` fix the
original order. No instance is introduced in this module.

The sole import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.ResidueCharacteristic`,
which supplies `residueCharacteristic` and, transitively, the published
`LocalField` package and `Nat.Prime`. The upstream imports are not used.

The published Library and the approved Mathlib were searched before
authoring; neither declares this target. Mathlib's
`CharP.prime_ringChar` (in `Mathlib.Algebra.CharP.Lemmas`) is the expected
proof ingredient, as in the source proof, but is not needed to state the
target.

## Attribution

The original copyright, Apache-2.0 release line and author header are
retained verbatim, followed by a modification notice. The unmodified
Apache-2.0 [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain in the Library, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
