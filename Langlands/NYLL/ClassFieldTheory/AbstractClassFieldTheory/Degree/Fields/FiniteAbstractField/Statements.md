# NYLL M010: extensionality target for finite abstract fields

The source is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`
(file SHA-256 `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`).
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original name | Source lines | Adapted name |
| --- | --- | --- | --- |
| M010.122 | `ClassFormation.FiniteAbstractField.eq_of_field_eq` | 1102–1111 | `Langlands.NYLL.ClassFormation.FiniteAbstractField.eq_of_field_eqStatement` |

The target keeps the source telescope exactly: implicit `{G : Type u}` with
`[Group G] [TopologicalSpace G]` from the section variable (source line 46),
explicit `(K L : FiniteAbstractField G)` and the explicit hypothesis
`(h : K.field = L.field)`, in that order. Its body is the source conclusion
`K = L`. It states that a finite abstract field (the published structure
`Langlands.NYLL.ClassFormation.FiniteAbstractField`, M010.121, from module
`Degree.Fields.FiniteAbstractField.Definitions`) is determined by its
underlying closed subgroup; the finiteness field is a proof.

Modifications by Worker 171: the source theorem is converted to
`def eq_of_field_eqStatement … : Prop := K = L`; the source proof (case
analysis on both structures, `cases h`, `rfl`) is omitted, since proofs of the
target are a separate proof task. The namespace is prefixed with
`Langlands.NYLL` and the only import is the published
`FiniteAbstractField` definitions module. The hypothesis `h` is not
referenced by the proposition `K = L` itself; it is kept because the source
statement has it and the target must keep every source hypothesis in the source
binder order (a proof of the target receives `h` as its premise).

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
