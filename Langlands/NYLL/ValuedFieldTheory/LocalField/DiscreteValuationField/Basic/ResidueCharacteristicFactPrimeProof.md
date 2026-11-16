# Primality of the residue characteristic as a typeclass fact: proof (M334.013)

This module proves the exact published closed target
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.residueCharacteristic.fact_primeStatement.{u, v}`.
Its theorem retains the adapted source name:

```lean
theorem residueCharacteristic.fact_prime :
    residueCharacteristic.fact_primeStatement.{u, v}
```

The namespace is
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`.
The independent universe parameters are `u v`, in that order. The theorem's
declared type is the named target itself, with no additional declaration
arguments. The target's Lean/Markdown pair and all its imports are unchanged.

## Scope and implemented proof

The target universally quantifies an implicit field `K : Type u`, its
`[Field K]` instance, and an explicit package `F : LocalField.{u, v} K`.
The package extends the published chosen complete discretely valued field,
with value group in universe `v`, by finiteness of its residue field.
The conclusion is `Fact F.residueCharacteristic.Prime`, where
`F.residueCharacteristic` is `ringChar F.residueField`. No hypothesis is
added and the conclusion is unchanged.

The complete proof is:

```lean
by
  intro K _ F
  exact ⟨F.residueCharacteristic_prime⟩
```

The first line introduces the target's binders, preserving their implicit,
instance and explicit roles in the target. The published theorem
`residueCharacteristic_prime`, at its closed target
`residueCharacteristic_primeStatement.{u, v}`, supplies the proof of
`Nat.Prime F.residueCharacteristic`. The notation
`⟨F.residueCharacteristic_prime⟩` constructs the `Fact` wrapper with this
proof as its `out` field; it is the unchanged source body.

The module then executes:

```lean
attribute [instance] residueCharacteristic.fact_prime
```

No priority is specified, so registration uses the default priority, as in
the source. The target is a reducible `abbrev`, allowing Lean to unfold its
quantifiers to the class `Fact` when registering the theorem. This preserves
the source instance interface for typeclass inference. `Fact` is
`Prop`-valued, so the registration introduces no data structure.

## Dependencies

The two direct imports are:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.ResidueCharacteristicFactPrimeStatement`,
  supplying the exact target and, transitively, `LocalField`,
  `residueCharacteristic`, `Fact` and `Nat.Prime`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.ResidueCharacteristicPrimeProof`,
  supplying the published proof `residueCharacteristic_prime` (M334.011).

The primality theorem uses the finite residue field's field structure and
Mathlib's `CharP.prime_ringChar`, as documented in its own paired Markdown.
This module only packages that published theorem; it does not repeat its
proof. Its proof does not call M334.010 `residueCharacteristic_ne_zero` or
M334.012 `residueField_charP_residueCharacteristic` (the latter is present
transitively through the target import). The upstream repository is not
imported.

## Source correspondence and modifications

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean#L100-L103).
The source file SHA-256 is
`69d3219d17ef6bef4204e02538d5a3f28ee63edb1bc1e0be2354bed4c739afe9`.

| Unit | Original declaration | Source locations | Adapted declaration |
| --- | --- | --- | --- |
| M334.013 | `LocalFieldTheory.DiscreteValuationField.LocalField.residueCharacteristic.fact_prime` | section variables 42; docstring 100; signature 101–102; body 103 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.residueCharacteristic.fact_prime` |

The source declares an `instance` with explicit argument
`(F : LocalField.{u, v} K)` under section variables
`{K : Type u} [Field K]`. Since `Fact` is a `Prop`-valued class, this is a
theorem-kind declaration. The published target records the complete source
telescope. This proof states a theorem at that target and registers it
separately with `[instance]`, following the published M239.005
`inertiaGroup_normal` precedent.

Worker 289 made these changes on 16 November 2026:

- extracted only M334.013 and prefixed the namespace with `Langlands.NYLL`;
- replaced the source signature by the exact published closed target and
  introduced its binders before the unchanged source body;
- expressed the source's default-priority instance registration as a
  separate `attribute [instance]` command;
- replaced the nine upstream imports with the two published modules above;
- omitted unused source universes `w x`, retained `u v` in their original
  order, and replaced the module documentation.

The source docstring, mathematical scope and proof term are retained.
Worker 125 supplied the proof route in the task context and is credited as
a coauthor.

## Attribution

The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The original copyright, Apache-2.0 release line and author header are
retained verbatim, followed by the modification notice. The existing
unmodified [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany the submission.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
