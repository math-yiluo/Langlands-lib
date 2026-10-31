# Equal norm subgroups identify classes of the same representative

`Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfNormSubgroupEq_normClass.{u}`
proves exactly the published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormQuotientEquivOfNormSubgroupEqNormClassStatement.{u}`.
The theorem's declared type is that unapplied statement constant. It has
no external term parameters. The proposition contains all ten binders:

```lean
∀ (K L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]
  (h : localNormSubgroup K L = localNormSubgroup K M) (x : Kˣ),
  normQuotientEquivOfNormSubgroupEq K L M h (normClass K L x) =
    normClass K M x
```

The three explicit field carriers share one arbitrary universe `u`.
Their three field structures and the two algebra structures are
instance-implicit. The equality `h` and base-field unit `x` are explicit.
This preserves the source order and binder kinds, with no restriction
to `Type 0` and no algebra structure from `L` to `M`.

The sole direct import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U013.Statements`.
Its pair and all 17 further imported Library pairs remain unchanged.
They supply `normUnits K L = Units.map (Algebra.norm K)`,
`localNormSubgroup K L = (normUnits K L).range`,
`NormQuotient K L = Kˣ ⧸ localNormSubgroup K L`, and the canonical
quotient homomorphism `normClass K L`. The analogous definitions for
`M` use the supplied `Algebra K M` structure. The U012 equivalence
`normQuotientEquivOfNormSubgroupEq K L M h` is the multiplicative
equivalence induced by the equality of these actual norm images.
The equation says that it sends the class of `x` in the `L` quotient
to the class of the same `x` in the `M` quotient.

The unrestricted Mathlib determinant norm is retained. In the approved
`Mathlib/RingTheory/Norm/Defs.lean`, lines 59–62 define `Algebra.norm`
without a finite-module premise, and lines 76–79 prove it constantly
`1` when the algebra is not a finite module. The theorem retains these
cases. It adds no finite-dimensionality, local-field, valuation,
topology, separability, Galois, surjectivity or exact-kernel assumption.
Normality is supplied by commutativity of `Kˣ`.

## Implemented proof

The proof first introduces the ten internal binders, using anonymous
names for the five structure instances. Definitional reduction of the
published U012 equivalence and the two class maps allows `change` to
expose precisely

```lean
QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) =
  QuotientGroup.mk x
```

The proof then applies `QuotientGroup.quotientMulEquivOfEq_mk h x`.
The approved Mathlib `GroupTheory/QuotientGroup/Basic.lean`,
lines 162–173, defines the equality-induced quotient equivalence and
proves this representative equation by reflexivity. No subgroup
membership, surjectivity or kernel theorem is needed. This is the
original proof after introduction of the closed target's binders.

## Original passage and adaptation

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
pinned at `fbd320cd8b1b06487c58227e92eb135794267709`.
The selected passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`,
lines 124–135](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L124-L135):
docstring 124–125, attribute 126, theorem 127–132 and proof 133–135.
The whole-file SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
Lines 1–180 were read, including the preceding quotient constructions.
The [partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093)
identifies this as M093.013, with no patch10 change.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.normQuotientEquivOfNormSubgroupEq_normClass` | `Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfNormSubgroupEq_normClass` |
| Original theorem's complete proposition | `Langlands.NYLL.LocalFieldTheory.NormQuotientEquivOfNormSubgroupEqNormClassStatement` |
| `LocalFieldTheory.normQuotientEquivOfNormSubgroupEq` | `Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfNormSubgroupEq` |
| `LocalFieldTheory.normClass` | `Langlands.NYLL.LocalFieldTheory.normClass` |
| `LocalFieldTheory.localNormSubgroup` | `Langlands.NYLL.LocalFieldTheory.localNormSubgroup` |

Only the first row introduces a declaration here. The other rows name
unchanged published dependencies. The namespace gains `Langlands.NYLL`,
and the theorem's type becomes the published closed statement constant.
After introducing its binders, the source proof is unchanged. The
duplicate docstring sentence, source `@[simp]` registration, unused
universe `v`, source-wide noncomputable section, original broad imports
and all other declarations are omitted. The sole import is U013
Statements. The theorem itself requires no noncomputable section.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`.
Its attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Source-ID errata locations in the workspace, project, current Library
and literature were checked; no applicable erratum was found.
Fresh TaskHub and native exact-name searches found no existing proof
besides this assigned task. Old verbatim upstream audit-draft copies
were not reused.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0 with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
The source calculation uses the same Mathlib interface at the approved
pin. Compilation, exact-target validation, independent semantic
review and Integrator publication supply distinct evidence.

This generic representative equation leaves parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38`'s named Artin map, exact norm
kernel, host quotient and evaluation adapters, and continuity
obligations open. M093.014 and later units remain separate.

## Attribution

The original copyright and author header is preserved verbatim:
copyright 2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted
by OpenAI Codex)”, released under Apache-2.0. A dated modification
record identifies Worker 107's adaptation. Worker 107 extracted this
proof directly from the pinned original and wrote its companion.
No other project worker supplied code or a reused draft.

The inherited [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) remain unchanged
and are included in `repository_paths`. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively, matching the pinned originals. The inherited NOTICE's
ValuedFieldTheory source list has no NormQuotient-specific third-party
entry. Existing dependency notices and attribution remain preserved.
