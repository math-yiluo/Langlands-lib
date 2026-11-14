# Primality of the residue characteristic: proof (M334.011)

The module proves NYLL unit M334.011 as the exact published closed
proposition `residueCharacteristic_primeStatement.{u, v}`. The public theorem
is
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.residueCharacteristic_prime`,
the source name with the `Langlands.NYLL` namespace prefix. Its complete
type is that target constant with universe parameters `u v` in that order
and no further declaration arguments:

```lean
theorem residueCharacteristic_prime : residueCharacteristic_primeStatement.{u, v}
```

The entry module is
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.ResidueCharacteristicPrimeProof`.
The published statement module `Basic.ResidueCharacteristicPrimeStatement`
and everything it imports are used unchanged.

## Statement proved

For every field `K : Type u` and every local-field package
`F : LocalField.{u, v} K` (a chosen complete discrete valuation on `K`, with
value group in universe `v`, whose residue field is finite), the residue
characteristic `F.residueCharacteristic = ringChar F.residueField` is a prime
number. No hypothesis is added and the conclusion is not weakened; the two
universes stay independent.

## Implemented proof

1. `intro K _ F` introduces the target's binders: the implicit field `K`,
   its `Field` instance and the package `F`.
2. `change Nat.Prime (ringChar F.toCompleteDVF.residueField)` unfolds the
   reducible abbreviations `residueCharacteristic` and
   `LocalField.residueField` to the residue field of the underlying complete
   discretely valued field. Through further published abbreviations this is
   Mathlib's `IsLocalRing.ResidueField` of the valuation subring, which
   carries Mathlib's `Field` instance.
3. A local instance `NoZeroDivisors F.toCompleteDVF.residueField` is supplied
   by `GroupWithZero.noZeroDivisors`, using that the residue field is a field
   and hence a group with zero.
4. Mathlib's `CharP.prime_ringChar` (in `Mathlib.Algebra.CharP.Lemmas`)
   states `Nat.Prime (ringChar R)` for a ring `R` with `NoZeroDivisors`,
   `Nontrivial` and `Finite` instances. `Nontrivial` comes from the field
   structure, and `Finite` from the package field `residueFinite`, which the
   published `Basic.Definitions` module registers as an instance. Internally
   the Mathlib lemma combines `CharP.ringChar_ne_zero_of_finite` (a finite
   ring has nonzero characteristic) with `CharP.char_prime_of_ne_zero` (a
   nonzero characteristic of a nontrivial ring without zero divisors is
   prime).

The proof does not use M334.010 `residueCharacteristic_ne_zero`, nor the
M334.012 instance `residueField_charP_residueCharacteristic`. The
development check reports only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Source correspondence and adaptations

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`
(SHA-256 `69d3219d17ef6bef4204e02538d5a3f28ee63edb1bc1e0be2354bed4c739afe9`).

| Unit | Original name | Source lines | Implementation here |
| --- | --- | --- | --- |
| M334.011 | `LocalFieldTheory.DiscreteValuationField.LocalField.residueCharacteristic_prime` | section variables 42, docstring 87, type 88–89, proof 90–93 | `residueCharacteristic_prime` with the exact closed target type |

The tactic body (source lines 90–93) is copied verbatim. The adaptations are:

- the namespace is prefixed with `Langlands.NYLL`;
- the source signature `(F : LocalField.{u, v} K) : Nat.Prime F.residueCharacteristic`
  under the section variables `{K : Type u} [Field K]` is replaced by the
  published closed target `residueCharacteristic_primeStatement.{u, v}`,
  whose body quantifies exactly these binders in the same order, so the proof
  begins with `intro K _ F`;
- the source imports are replaced by the published statement module and
  `Mathlib.Algebra.CharP.Lemmas` (the module that provides
  `CharP.prime_ringChar`), and the unused universes `w` and `x` of source
  line 27 are not declared;
- the docstring mentions the local-field package explicitly, and the module
  documentation is new.

## Imports and scope

Direct imports:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.ResidueCharacteristicPrimeStatement`,
  the published target, which transitively supplies `LocalField`, its
  `Finite` residue-field instance and `residueCharacteristic`;
- `Mathlib.Algebra.CharP.Lemmas`, for `CharP.prime_ringChar`.

This module adds only the theorem above: no instance, hypothesis or axiom.
The `Fact` instance M334.013, which consumes this theorem, belongs to a
separate unit of Task 6058.

## Attribution

The registered source `external-lean-reuse-snapshots-2026-10-21` (content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) retains
the original at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The original copyright, Apache-2.0 release line and author header (copyright
2026 Naganori Yamaguchi; authors Naganori Yamaguchi, assisted by OpenAI
Codex) are retained verbatim, followed by a modification notice by
Worker 461 dated 2026-11-14. The unmodified Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany this adaptation,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 125 recorded and compiled this route in the task context; Worker 461
wrote the module and this Markdown. The approved environment is
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
