# Galois actions on field units and the integer value group

This pair extracts M140.001 and M140.005 as actual data. Within namespace
`Langlands.NYLL.LocalClassFieldTheory`, each has the source telescope
`(K L : Type u) [Field K] [Field L] [Algebra K L]`, with the same arbitrary
shared universe `u`, explicit field binders and instance binders in that order.
No finite-dimensionality or Galois-extension hypothesis is added. `Gal(L/K)`
is the actual automorphism group `L ≃ₐ[K] L` even without such a hypothesis.

| Unit | Original name after `LocalClassFieldTheory.` | Adapted name after `Langlands.NYLL.LocalClassFieldTheory.` | Source lines |
| --- | --- | --- | --- |
| M140.001 | `galoisGroupFieldUnitsMulDistribMulAction` | `galoisGroupFieldUnitsMulDistribMulAction` | 29–35 (command 32) |
| M140.005 | `galoisGroupValueGroupMulDistribMulAction` | `galoisGroupValueGroupMulDistribMulAction` | 78–88 (command 81) |

`galoisGroupFieldUnitsMulDistribMulAction K L` has result
`MulDistribMulAction (Gal(L / K)) Lˣ` and retains the exact source body
`inferInstance`. This reuses Mathlib's canonical algebra-automorphism action
on the field and its induced action on actual field units.

`galoisGroupValueGroupMulDistribMulAction K L` has result
`MulDistribMulAction (Gal(L / K)) (Multiplicative Int)`. Its source structure
body is unchanged: `smul _ n := n`, and each of `one_smul`, `mul_smul`,
`smul_mul`, `smul_one` uses the source introduction and `rfl` proof.
These are definitions with `@[implicit_reducible]`, exactly as in the source,
and are not global instances. Consumers choose the action using local `let`
instances. The value group is the actual `Multiplicative Int`, not a supplied
abstract group or a replacement representation.

## Modifications and imports

The only changes to the data are the namespace prefix, extraction into this
file, adjusted explanatory comments and imports. Both construction bodies and
their proof fields are verbatim. Source theorems are absent from this file;
the source M140.002 action-evaluation proof is not needed by these definitions.
The imports use Mathlib's algebra equivalences, unit actions, Galois groups and
local-field notation, plus the published integer-unit inclusion module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions`.
The latter also gives the adjacent statement module the existing NYLL namespace.
There are no private, anonymous or local source commands requiring new names.

This data does not assert class formation or reciprocity, and no source theorem
is established here. Development compilation used approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` with no diagnostics.

## Source and attribution

The pinned original is Naganori Yamaguchi's NYLL project at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean`
(file SHA-256 `478460e530e2a37ae4dc4eaad7db80d4dfa290f5bdd715a66d507ab2539579e0`).
The complete source module, lines 1–265, was read. It is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean`.

The registered sources are `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum appears in `notes/errata/`.
The original copyright and author header is preserved verbatim, including
Naganori Yamaguchi (assisted by OpenAI Codex). The original Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain in the Library.
Worker 230 made this extraction and wrote its documentation on 13 November 2026.
The source-to-port changes are recorded below. No source-specific NOTICE entry
is changed, and no Mathlib implementation is copied.
