# Field principal-unit antitonicity

This module proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.fieldPrincipalUnits_antitoneStatement`
with the theorem
`Langlands.NYLL.LocalClassFieldTheory.fieldPrincipalUnits_antitone`.
Its type is exactly that closed proposition. Expanding it gives

```lean
∀ (K : Type) [Field K] [ValuativeRel K] {m n : ℕ},
  m ≤ n →
    Langlands.NYLL.LocalFieldTheory.fieldPrincipalUnits K n ≤
      Langlands.NYLL.LocalFieldTheory.fieldPrincipalUnits K m
```

The field is in `Type 0`, as in the target and original theorem; there are no
universe parameters. The two indices may be zero. The only hypotheses are a
field, a supplied valuative relation, and the inequality of indices. No
topology, local-field, discreteness, completeness, residue-field, extension,
or Artin-map hypothesis is introduced.

## Implemented proof

The theorem imports the published
[statement](Statements.md) without editing it or its dependencies. The
published `fieldPrincipalUnits K r` is the image of the actual valuation-ring
subgroup `principalUnits K r` under the canonical homomorphism on units. Its
source subgroup has the defining membership condition
`((u : 𝒪[K]) - 1) ∈ (𝓂[K] ^ r : Ideal 𝒪[K])`.

After introducing the target's binders and `hmn : m ≤ n`,
`Subgroup.map_mono` reduces the field-unit inclusion to the corresponding
integer-unit subgroup inclusion. Introducing an integer-ring unit `u` and
its membership proof `hu`, the proof applies
`Ideal.pow_le_pow_right hmn hu`. This uses
`𝓂[K] ^ n ≤ 𝓂[K] ^ m` to keep the same difference `u - 1` in the smaller
power index. Subgroup membership unfolds definitionally, so no separate
membership or integer-unit antitonicity theorem is needed.

The implementation adds exactly this one theorem; it introduces no helper,
instance, replacement filtration, or further conductor result.

## Source correspondence and modifications

The source is Naganori Yamaguchi's NYLL `ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The relevant passages are:

| Source passage | Reuse in this proof |
| --- | --- |
| [`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Conductor.lean`, lines 34–39](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Conductor.lean#L34-L39), M290.001 | Original `LocalClassFieldTheory.fieldPrincipalUnits_antitone`, including its Type 0 scope and `Subgroup.map_mono` argument. |
| [`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean`, lines 79–84](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean#L79-L84), M131.005 | The integer-unit inclusion proof `intro u hu; exact Ideal.pow_le_pow_right h hu`, inlined into the field theorem. |

Both passages and their surrounding section binders were read directly from
the registered snapshot at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The complete source files have SHA-256
`8000c3bea736ec102e4c879ad0da46d84eaae22d8091861493085966ce05c82c`
and
`1b36c019d270961f321ca891ae155fb4fd658d4e29ed97ba78e30fbee00a5047`,
respectively. The source registrations are
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable errata file for either registration was found in the supplied
Library's `notes/errata`.

Worker 322 made the following adaptations:

- Prefix the source namespace with `Langlands.NYLL`, retaining the original
  theorem name and docstring.
- Type the theorem directly by the published closed proposition and introduce
  its field, instance and index binders in the proof.
- Inline the source integer-unit helper M131.005 instead of importing or
  introducing a theorem under that helper's name.
- Replace the broad source imports by the focused published `Conductor.Statements`
  module, and omit the unused notation scope, namespace opening and
  noncomputable section.
- Replace the conductor-wide module documentation by documentation of this proof,
  and record the adaptations in the source comment.

The actual valuation ring, maximal ideal, principal-unit subgroup and field-unit
image remain the published definitions. The canonical inclusion wrapper already
unfolded by the published field-unit definition needs no further change here.
Neither selected source module has an applicable patch10 compatibility edit;
no modified implementation draft from another worker is reused.

The original copyright and author header is preserved. The unchanged
Apache-2.0 [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain in the Library, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No additional third-party implementation is copied.

## Development validation

Focused Lean service check `85b50dd5-a4e3-4337-a234-90b99ba46c62` compiled
this proof and inspected the theorem in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). It returned `ok: true`, exit
code zero, and zero errors or warnings. Inspection reports a theorem with
no universe parameters and only `propext`, `Classical.choice` and `Quot.sound`.
The source project targeted Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
This development check is separate from exact-target submission validation,
independent semantic review and integration.
