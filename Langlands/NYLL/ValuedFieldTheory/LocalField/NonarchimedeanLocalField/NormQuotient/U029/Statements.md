# Norm-image membership gives trivial norm class

This module defines the single closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassEqOneOfMemStatement.{u} : Prop`.
It records the asserted type of M093.029 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Its sole direct import is the public
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U028.Proofs`.
That module and its entire published dependency chain remain unchanged.

## Complete closed telescope

The definition has no external term or instance parameters and retains
exactly one arbitrary universe `u`. Its entire body is

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
  {x : Kˣ} (hx : x ∈ localNormSubgroup K L), normClass K L x = 1
```

All seven binders are internal to the proposition, in this order:

| Binder | Kind and meaning |
| --- | --- |
| `K : Type u` | Explicit base field type |
| `L : Type u` | Explicit extension field type in the same universe |
| `[Field K]` | Instance-implicit field structure on `K` |
| `[Field L]` | Instance-implicit field structure on `L` |
| `[Algebra K L]` | Instance-implicit algebra structure |
| `{x : Kˣ}` | Implicit representative in the base-field unit group |
| `(hx : x ∈ localNormSubgroup K L)` | Explicit membership witness |

The last binder expresses the implication from norm-image membership to
triviality of the norm class. It is quantified inside the proposition;
it is not an assumed parameter of the definition. The representative
remains implicit, as in the source. The unused-variable linter is disabled
only for this definition to retain the original name `hx`: the conclusion
does not depend on the particular membership proof. This setting does not
change the proposition. There is no finite-dimensionality,
finite-module, valuation, topology, local-field, separability or Galois
premise. The module's local-field location does not restrict this
generic algebraic assertion.

## Actual norm subgroup and canonical map

The public `Langlands.NYLL.LocalFieldTheory.normUnits`, in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`,
is `Units.map (Algebra.norm K) : Lˣ →* Kˣ`. Its field universes are
independent, and it has no finiteness premise. The public
`localNormSubgroup`, in `NormQuotient.U001.Definitions`, is exactly
`(normUnits K L).range`, here specialized to the shared universe `u`.
Consequently membership of `x` means there is a unit of `L` whose unit
norm equals `x`.

The public `NormQuotient`, in U002.Definitions, is
`Kˣ ⧸ localNormSubgroup K L`, with its existing U003 commutative-group
structure. The public `normClass`, in U005.Definitions, is the canonical
homomorphism `QuotientGroup.mk' (localNormSubgroup K L)`. Thus the
conclusion is equality to the identity of this actual quotient. These
constructions are reused unchanged.

The host `Langlands.LocalClassField.NormQuotient` has a
finite-dimensionality parameter and does not replace this general
support interface.

## Assertion and deferred truth proof

This file defines the proposition and contains no proof of its truth.
The later exact proof is reserved as
`Langlands.NYLL.LocalFieldTheory.normClass_eq_one_of_mem`, with type
`NormClassEqOneOfMemStatement.{u}`. No instance or simp registration is
installed here.

The already public `normClass_eq_one_iff_mem` in
`NormQuotient.U022.Proofs` proves `NormClassEqOneIffMemStatement.{u}`,
whose body is

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Kˣ),
  normClass K L x = 1 ↔ x ∈ localNormSubgroup K L
```

It is inherited through the unchanged U028 chain. The source proof of
M093.029 applies the reverse direction of this equivalence to `hx`.
This records the source proof route and available public dependency;
the separate truth proof remains deferred.

## Pinned original and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:262–266`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L262-L266):
docstring at 262, theorem and complete telescope at 263–264, asserted
conclusion at 265, and omitted proof at 266. Its asserted type is

```lean
theorem normClass_eq_one_of_mem (K L : Type u) [Field K] [Field L]
    [Algebra K L] {x : Kˣ} (hx : x ∈ localNormSubgroup K L) :
    normClass K L x = 1
```

The complete original file was read; its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The norm subgroup, quotient and canonical projection are at 26–54,
and the reused equivalence is at 206–211. The support norm originates
in `Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`.
That complete original file was also read; its SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Telescope and asserted conclusion of `normClass_eq_one_of_mem` | Closed `NormClassEqOneOfMemStatement.{u}`, defined here |
| `localNormSubgroup` and `normUnits` | Existing public norm-image constructions, unchanged |
| `NormQuotient` and `normQuotientCommGroup` | Existing public quotient and group structure, unchanged |
| `normClass` | Existing public canonical projection, unchanged |
| `normClass_eq_one_iff_mem` | Existing public U022.Proofs theorem, unchanged |
| Truth proof of `normClass_eq_one_of_mem` | Deferred exact theorem with the adapted source name |

Worker 107 extracted the asserted type directly from the pinned original
on 1 November 2026 and wrote this companion. The namespace gains the
`Langlands.NYLL` prefix and all seven original binders move inside a
closed Prop-valued definition, preserving their order and binder kinds.
The sole U028.Proofs import preserves the published chain. The truth
proof, original noncomputable section, unused universe `v` and unrelated
declarations are omitted. M093 has no patch10 change. No shared
adaptation draft or another worker's unpublished work was reused.

The retained originals belong to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Both source-ID errata paths were checked in the workspace, project and
supplied Library; none exists.

The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Attribution and remaining obligations

The original 2026 Naganori Yamaguchi copyright and author header is
retained verbatim, including “Naganori Yamaguchi (assisted by OpenAI
Codex)”, with an explicit dated modification record. There are no other
project coauthors or reused-draft contributors; dependency authors and
notices remain unchanged. The inherited Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained unchanged
through `repository_paths`. Their respective SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`;
they match the originals, including inherited dependency notices.

The exact truth proof requires a separate proof phase after this
statement is independently accepted and published. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains one named
`abelianLocalArtinMap` family for every prime and arbitrary supplied
`TF`/`TE`, with the actual unit-norm image, exact norm kernel, quotient
topology, finite discrete Galois topology, host quotient construction,
evaluation, bijectivity and both continuity directions. Type 0 is the
initial host stage and does not discharge arbitrary-universe transport.
This generic support statement supplies no normalization, inertia,
universe transport, cohomological comparison or reciprocity theorem.
Existing cohomological definitions and frozen targets retain their
meaning. M093.030 and later units and host adapters remain separate work.
Compilation alone establishes neither independent semantic acceptance
nor publication.
