# Equality of norm classes and multiplication by an inverse

The theorem
`Langlands.NYLL.LocalFieldTheory.normClass_eq_iff_mul_inv_mem`
proves the independently published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassEqIffMulInvMemStatement.{u}`.
Its entire unapplied type is that proposition, with no external term or
instance parameters. This is the proof of M093.037 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U037.Statements`.
That published Lean/Markdown pair and its complete imported chain are
preserved unchanged.

## Target and mathematical meaning

Unfolding the published assertion gives

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x y : Kˣ),
  normClass K L x = normClass K L y ↔ x * y⁻¹ ∈ localNormSubgroup K L
```

All seven binders remain internal, in their original order and kinds:

| Position | Binder | Kind |
| --- | --- | --- |
| 1 | `K : Type u` | explicit |
| 2 | `L : Type u` | explicit |
| 3 | `[Field K]` | instance-implicit |
| 4 | `[Field L]` | instance-implicit |
| 5 | `[Algebra K L]` | instance-implicit |
| 6 | `x : Kˣ` | explicit |
| 7 | `y : Kˣ` | explicit |

The sole universe parameter `u` is arbitrary and shared by the fields.
The left side equates their canonical quotient projections. On the right,
the inverse and multiplication are taken in the unit group `Kˣ`, with `x`
as the left factor and `y⁻¹` as the right factor. Both implications are
proved. Applying `normClass_eq_iff_mul_inv_mem K L x y` gives this
equivalence; `.1` and `.2` give its respective directions.

The unchanged inherited constructions are

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L = QuotientGroup.mk' (localNormSubgroup K L)
```

Here the last identity is understood through the named quotient type.
These constructions come respectively from NormUnits.U002.Definitions and
NormQuotient.U001.Definitions, U002.Definitions and U005.Definitions under
the imported support prefix. U003.Definitions supplies the quotient
commutative group structure. Thus the membership condition means that
some extension unit `z : Lˣ` has `normUnits K L z = x * y⁻¹`. Equal classes
are precisely representatives whose ordered quotient lies in this actual
norm image.

There are no finite-dimensionality, finite-module, local-field, valuation,
topology, separability or Galois premises. The general algebra norm
convention is inherited without restriction. The separate host norm
quotient with its finite-dimensionality parameter is not used.

## Implemented proof

The complete proof body is

```lean
  intro K L _ _ _ x y
  simpa [div_eq_mul_inv] using normClass_eq_iff_div_mem K L x y
```

The introductions expose all seven internal binders, with the three
structures available as local instances. The inherited public theorem
`Langlands.NYLL.LocalFieldTheory.normClass_eq_iff_div_mem` from
NormQuotient.U019.Proofs has unapplied type
`NormClassEqIffDivMemStatement.{u}`. At `K L x y` it gives the same
left side and the membership condition `x / y ∈ localNormSubgroup K L`.
The group identity `div_eq_mul_inv` rewrites that quotient to `x * y⁻¹`.
Simplification therefore produces exactly the required equivalence, in
both directions and with the prescribed factor order. This is the
original proof route, preceded by the introductions needed for the
closed proposition. No helper declaration, additional premise, instance
or simp registration is added.

## Pinned original and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:327–333`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L327-L333).
Lines 327–328 are the retained docstring, 329 introduces the theorem and
`K L`, 330 gives the three instances and explicit representatives,
331–332 give the equivalence, and 333 is the retained `simpa` proof.
The whole-file SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The original division-form theorem and proof are at lines 183–190,
and the subgroup, quotient, group structure and projection at lines 26–54.

The actual unit norm is at lines 32–34 of
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`, whose whole-file SHA-256
is `1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.
Worker 1153 read both complete retained originals and recomputed their
hashes on 5 November 2026 UTC.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Asserted type of `normClass_eq_iff_mul_inv_mem` | Published closed `NormClassEqIffMulInvMemStatement.{u}` in U037.Statements |
| Proof `normClass_eq_iff_mul_inv_mem` | This theorem of the same adapted name in U037.Proofs |
| `normClass_eq_iff_div_mem` | Published U019.Proofs theorem reused through the unchanged import chain |
| `normUnits`, `localNormSubgroup`, `NormQuotient`, `normClass` | Existing public constructions with their original meanings |

The adaptation prefixes the namespace, replaces the source imports by the
sole published U037.Statements import, and names the closed published
proposition as the theorem type. The seven introductions recover the
original context before its unchanged proof step. The unused universe
`v`, noncomputable section and other source declarations are omitted.
The partition places this unit after M093.036.END. No patch10 edit applies
to M093, and no unpublished project draft is reused. Worker 1560 authored
the imported statement pair; Worker 1153 authored this proof pair directly
from the pinned original and published dependencies. There are no project
coauthors for this pair.

The retained original is in registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Both source-ID errata paths were checked under `notes/errata/` in the
workspace, project and supplied Library on 5 November 2026 UTC; all six
paths were absent.

## Attribution, environment and scope

The Lean file preserves the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 1153's dated modification
record. The inherited [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE), including applicable
dependency attribution, remain unchanged in `repository_paths`.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching the pinned originals. No Mathlib source is copied.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Development compilation is
separate from acceptance. Publication under `lean.proof@1` requires the
Lake/kernel/exact-target, unchanged-statement and frozen-dependency checks,
independent semantic review and Integrator publication.

This proof covers the generic algebraic support identity M093.037.
M093.038 onward and host adapters remain separate. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains the named Artin family,
exact norm kernel, surjectivity, host quotient evaluation and bijectivity,
actual quotient topology, finite discrete Galois topology and both
continuity directions for every prime and arbitrary supplied `TF` and `TE`.
Type 0 is an intermediate host stage. Normalization, inertia, universe
transport and comparison with the cohomological route remain separate
obligations. Existing cohomological definitions and frozen targets keep
their meanings.
