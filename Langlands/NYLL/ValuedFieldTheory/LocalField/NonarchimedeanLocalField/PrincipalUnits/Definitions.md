# Principal-unit subgroups of valuation-ring units

This module defines `Langlands.NYLL.LocalFieldTheory.principalUnits`. For an
arbitrary field `K : Type u` with a supplied `ValuativeRel K`, let
`O = Valuation.integer (ValuativeRel.valuation K)` and let
`m = IsLocalRing.maximalIdeal O`. For each natural number `n`, the definition
is the subgroup of `Oˣ` whose underlying set is

\[
\{a\in O^\times\mid a-1\in\mathfrak m^n\}.
\]

The ring, units, maximal ideal and ideal powers are the actual canonical
Mathlib constructions. With `open scoped ValuativeRel`, its complete interface
is

```lean
principalUnits.{u} (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
  Subgroup 𝒪[K]ˣ
```

The carrier is definitionally
`{a | ((a : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])}`.
The arbitrary universe and the supplied valuation relation are retained.
There is no topology, local-field, discrete-valuation, nontrivial-valuation,
completeness, prime or finite-dimensionality hypothesis. All natural indices,
including zero, are permitted. There is no additional lower bound on `n`.
No statement equating the zeroth subgroup to the top subgroup is introduced
here; its separate target and proof belong to later work.

## Intrinsic subgroup certificates

The three proofs inside the subgroup constructor are exactly the source
certificates. They work in the integer ring with `I = m^n`.

- The identity belongs because `1 - 1 = 0` and every ideal contains zero.
- Products belong by `ab - 1 = (a - 1)b + (b - 1)`, closure under multiplication
  by ring elements, and closure under addition.
- Inverses belong by `a⁻¹ - 1 = -(a⁻¹(a - 1))`, using `Units.inv_mul`,
  closure under multiplication by ring elements, and closure under negation.

The two polynomial identities use `ring`. These certificates only construct
the subgroup; this file introduces no separate membership, order, quotient,
automorphism or reciprocity theorem, and installs no new global instance.

## Source and exact adaptation

The original is Naganori Yamaguchi's NYLL `ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean#L19-L50),
lines 19–50 (the declaration starts at line 24). Its SHA-256 is
`1b36c019d270961f321ca891ae155fb4fd658d4e29ed97ba78e30fbee00a5047`.
This is exactly unit M131.001 of the published NYLL declaration partition.

| Original | Adapted |
| --- | --- |
| `LocalFieldTheory.principalUnits` | `Langlands.NYLL.LocalFieldTheory.principalUnits` |

The original namespace is prefixed with `Langlands.NYLL`. The declaration,
carrier and constructor proof bodies are unchanged. The original broad module
documentation is replaced by documentation of this single definition. Only the
universe, notation scope, noncomputable section and this declaration are
retained; source theorem commands beginning at line 54 are excluded.
The source import
`Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic` is replaced by
these direct imports:

- `Mathlib.Topology.Algebra.Valued.ValuativeRel`
- `Mathlib.RingTheory.Ideal.Operations`
- `Mathlib.Tactic.Ring`

The first supplies the canonical valuation and integer/maximal-ideal notation;
the second supplies ideal operations and powers; the third supplies `ring`.
There are no project or other NYLL imports. This focused construction does not
port the normalized valuation or compactness results in the source's `Basic`.
No patch10 edit or other worker's implementation draft was reused.

The original is registered as `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original file was read directly from the registered snapshot; no applicable
errata file was found in the supplied project notes or published Library.
The source copyright and author header is preserved. The unchanged upstream
Apache-2.0 [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are already present in the
Library. Their SHA-256 values are, respectively,
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The selected source path is not listed in the root NOTICE or the supplied
ValuedFieldTheory third-party attribution table. No additional third-party
source is copied by this module.

## Reuse boundary

Mathlib's `ValuationSubring.principalUnitGroup` is a subgroup of field units
with a strict valuation inequality, describing the first principal-unit step.
It does not supply the present natural-indexed subgroup of integer-ring units.
The host `Langlands.PadicField.TopologicalData.congruenceUnits` in
`Langlands.ClassFieldTheory.Local.Units` is a reduction kernel on integer-ring
units, parametrized by supplied p-adic field data; `unitFiltration` is its image
in field units. Its published `mem_congruenceUnits_iff` confirms the congruence
interpretation in that setting. The host
`Langlands.PadicField.TopologicalData.principalUnits` in
`Langlands.HarmonicAnalysis.Conductor` instead uses the discrete valuation and
has a field-unit codomain. Neither host interface preserves this definition's
arbitrary `Field`/`ValuativeRel` input signature directly.

A generic kernel of `Units.map (Ideal.Quotient.mk I).toMonoidHom` can represent
congruence units, but its carrier is expressed as equality in quotient units.
Retaining the source's direct ideal-membership carrier preserves its
computational presentation and the later reflexive membership target.
The canonical Mathlib ideal, ring, local-ring and units structures are reused
without duplication. This module adds no comparison with host filtrations,
Artin map, inertia theorem or local reciprocity assertion.

## Focused development check

The project Lean service successfully built this module and inspected the
unapplied declaration in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Development check
`5f0944d1-38f9-472e-a33e-9f21b8d80aaf` returned `ok: true`, exit code zero,
and zero errors or warnings. Inspection identified a definition with universe
parameter `u` and only the standard assumptions `propext`, `Classical.choice`
and `Quot.sound`. This establishes the stated three-import build; it is not
independent semantic acceptance or a proof of any later filtration theorem.
