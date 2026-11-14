# Primality of the residue characteristic as a typeclass fact: statement target (M334.013)

This module defines one closed proposition target in
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`:
`residueCharacteristic.fact_primeStatement.{u, v} : Prop`. It is the type of
the source instance `residueCharacteristic.fact_prime` (unit M334.013), with
the complete source telescope universally quantified inside the proposition in
its original order and with its original implicit, instance and explicit
binder kinds. Universe parameters `u v` are arbitrary and keep the source
order. This file supplies the statement only. Its proof is a separate
`lean.proof@1` task, whose theorem keeps the source name
`residueCharacteristic.fact_prime` and is registered as an instance.

## Complete proposition

```lean
abbrev residueCharacteristic.fact_primeStatement.{u, v} : Prop :=
  ∀ {K : Type u} [Field K] (F : LocalField.{u, v} K),
    Fact F.residueCharacteristic.Prime
```

For every field `K` in universe `u` and every local-field package
`F : LocalField.{u, v} K` (the published shared structure: a chosen complete
discrete valuation on `K` with value group in universe `v` and a finite
residue field), the proposition `Fact (Nat.Prime F.residueCharacteristic)`
holds. Here `F.residueCharacteristic = ringChar F.residueField` is the
published abbreviation (M334.009), and `F.residueCharacteristic.Prime` is
`Nat.Prime F.residueCharacteristic` by dot notation on `ℕ`. `Fact p` is
Mathlib's `Prop`-valued wrapper class (`Fact.out : p`) that lets typeclass
inference supply `p`, for example the hypothesis `[Fact p.Prime]` of Mathlib's
field structure on `ZMod p`. The field universe `u` and the value-group universe
`v` are independent. No hypothesis is added and the conclusion is unchanged.

Mathematically the content is that of M334.011: the residue field is finite,
so its characteristic is prime. The published theorem
`LocalField.residueCharacteristic_prime`
(target `residueCharacteristic_primeStatement`) already proves the unwrapped
form; this target only records the source's `Fact` packaging.

### Why a target and an `abbrev`

`Fact` is a `Prop`-valued class, so Lean elaborates the source `instance` as a
theorem-kind declaration. Following the route for source theorems, the type is
published here as a `Statement` target, and its proof follows in a
`lean.proof@1` task. The target is an `abbrev` (reducible), so that the proof
`theorem residueCharacteristic.fact_prime : residueCharacteristic.fact_primeStatement.{u, v}`
can be registered with `attribute [instance]`: instance registration unfolds the
reducible target to the telescope ending in the class `Fact`. The Library
precedent is the M239.005 target `inertiaGroup_normalStatement` and its proof
module `HilbertRamification/ValuationSubring/InertiaGroupNormalProof`. A draft
proof in this form, `intro K _ F; exact ⟨F.residueCharacteristic_prime⟩`, was
compiled together with this module. It registered the instance, and
`inferInstance` then found `Fact F.residueCharacteristic.Prime` and
`Field (ZMod F.residueCharacteristic)`. That draft is not part of this
candidate.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean#L100-L103).
The original file SHA-256 is
`69d3219d17ef6bef4204e02538d5a3f28ee63edb1bc1e0be2354bed4c739afe9`.
The readable original is kept under the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The recorded patch10 does not change this source module.

| Unit | Original name | Source lines | Adapted target |
| --- | --- | --- | --- |
| M334.013 | `LocalFieldTheory.DiscreteValuationField.LocalField.residueCharacteristic.fact_prime` | docstring 100, type 101–102, body 103 | `residueCharacteristic.fact_primeStatement` |

The source declaration is

```lean
instance residueCharacteristic.fact_prime (F : LocalField.{u, v} K) :
    Fact F.residueCharacteristic.Prime :=
  ⟨F.residueCharacteristic_prime⟩
```

under the section variables `{K : Type u} [Field K]` (line 42) in namespace
`LocalFieldTheory.DiscreteValuationField.LocalField`. The target quantifies
these section variables first, then the explicit `F`, exactly as in the
elaborated type of the source instance.

## Adaptation and reuse

Worker 125 made these changes on 14 November 2026:

- extracted the type of the source instance;
- prefixed the namespace with `Langlands.NYLL` and suffixed the name with
  `Statement`;
- moved the complete source telescope, including the section variables, into
  the proposition body;
- declared the target as an `abbrev`, for instance registration of its proof.

The formula, binder kinds and order are unchanged. The source body (line 103)
and the instance attribute are omitted. Explicit universe parameters `.{u, v}`
fix the original order. This module introduces no instance.

The sole import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.ResidueCharacteristic`.
It supplies `residueCharacteristic` and, transitively, the published
`LocalField` package, `Nat.Prime` and `Fact`. The upstream imports are not used.

The published Library and the approved Mathlib were searched before
authoring. Neither declares this target. No Library or Mathlib instance
provides `Fact (Nat.Prime (ringChar R))` for an arbitrary or residue-field `R`,
so the later instance will not compete with an existing one. Because `Fact` is
`Prop`-valued, it carries no data and cannot create a diamond.

An earlier attempt submitted the source instance itself as a definition
candidate (`0dd22c19-41ae-47e7-a259-da3f978f8a32`). Machine validation rejected
it, because a theorem-kind declaration is not a Lean definition. This target
and its proof task replace that attempt.

## Attribution

The original copyright, Apache-2.0 release line and author header are
retained verbatim, followed by a modification notice. The unmodified
Apache-2.0 [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain in the Library, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
