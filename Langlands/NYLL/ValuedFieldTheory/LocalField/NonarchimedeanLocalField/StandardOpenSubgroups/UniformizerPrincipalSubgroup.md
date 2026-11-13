# Standard uniformizer-principal subgroups

This module defines
`Langlands.NYLL.LocalFieldTheory.uniformizerPrincipalSubgroup`.
Its complete interface, with `open scoped ValuativeRel`, is

```lean
uniformizerPrincipalSubgroup.{u}
    (K : Type u) [Field K] [ValuativeRel K]
    (ϖ : Kˣ) (d n : Nat) : Subgroup Kˣ
```

The exact body is

```lean
Subgroup.zpowers (ϖ ^ d) ⊔ fieldPrincipalUnits K n
```

Here `Subgroup.zpowers (ϖ ^ d)` consists of the integer powers of `ϖ ^ d`.
The second factor is the published
`Langlands.NYLL.LocalFieldTheory.fieldPrincipalUnits K n`, the image in
`Kˣ` of the `n`-th principal-unit subgroup of valuation-ring units.
The supremum is the least subgroup containing both factors. Since `Kˣ`
is commutative, it also represents their subgroup product.

The universe `u` is arbitrary, and both natural indices include zero.
The parameter `ϖ` is any supplied unit: this definition imposes no
uniformizer or valuation-normalization condition. Its only instance
parameters are `Field K` and `ValuativeRel K`; it requires no topology or
local-field hypothesis.

## Source correspondence and modifications

The source is Naganori Yamaguchi's NYLL `ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/StandardOpenSubgroups.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/StandardOpenSubgroups.lean#L36-L42),
lines 36–42: the docstring is at lines 36–37 and the complete definition
command is at lines 38–42. The file's SHA-256 is
`9cf6baf50519f650504762782a5aed12500479b911fc1ac4db9a138207097d7d`.
This is exactly unit M289.002 in the published declaration partition.
The source's noncomputable section, namespace, scoped opening and universe
declaration at lines 19–28 were read with the command.

| Source | Adapted |
| --- | --- |
| `LocalFieldTheory.uniformizerPrincipalSubgroup` | `Langlands.NYLL.LocalFieldTheory.uniformizerPrincipalSubgroup` |
| `LocalFieldTheory.fieldPrincipalUnits` | Published `Langlands.NYLL.LocalFieldTheory.fieldPrincipalUnits` |
| `(d n : ℕ)` | `(d n : Nat)` |

Worker 322 extracted this command into a separate focused module, prefixed
the namespace with `Langlands.NYLL`, and spelled the natural-number type
as `Nat`. The original docstring, parameter order, arbitrary universe,
instance hypotheses and definition body are preserved. The source's
unused namespace openings are omitted, and its broad
`PrincipalUnitQuotients` import is replaced by the published
`StandardOpenSubgroups.Definitions` and Mathlib's
`Algebra.Group.Subgroup.ZPowers.Basic`.
The module documentation and modification comments describe this extraction.
No external implementation draft was copied; the existing published
`fieldPrincipalUnits` is imported by Lean name without editing its pair.

The original passages were read from the retained source snapshot at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its registration is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable source erratum was found in the supplied Library's errata notes.

The original copyright and author header is retained. The published
Apache-2.0 [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged and match
the pinned originals, with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Scope and validation

This module adds exactly the displayed definition, reusing Mathlib's
integer-power subgroup and subgroup supremum. It adds no global instances.
Every other definition, proposition target and theorem of the source module
is outside this contribution.

The focused development check uses the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Check `4406b614-ae9b-41ad-804e-2532389c0810` returned `ok: true` and
exit code zero, with no errors or warnings. It compiled the focused module
and private diagnostics that assign the complete unapplied declaration
to the displayed telescope and check the exact body by reflexivity at
arbitrary indices and at `d = n = 0`.
The printed declaration and inspection retained exactly the universe
parameter `u`; inspection identified a definition using only the standard
assumptions `propext`, `Classical.choice` and `Quot.sound`.
The diagnostics are private and excluded from the contribution.
This development check is separate from independent semantic acceptance
and Library publication.
