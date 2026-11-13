# NYLL M010: residue-degree target for the distinguished base field

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
| M010.128 | `ClassFormation.FiniteAbstractField.base_residueDegree` | 1181–1188 | `Langlands.NYLL.ClassFormation.FiniteAbstractField.base_residueDegreeStatement` |

The target keeps the source telescope exactly. It takes implicit
`{G : Type u}` with `[Group G] [TopologicalSpace G]` from the section variable
(source line 46), universe `u` (source line 30), and the explicit
`(D : DegreeData G)`. Its body is the source conclusion
`(FiniteAbstractField.base G).residueDegree D = 1`, an equation in `ℕ+`.

It says the following. Take the distinguished base field, bundled as a finite
abstract field (`FiniteAbstractField.base G`, M010.123, module
`Degree.Fields.FiniteAbstractField.Definitions`). Its positive absolute residue
degree with respect to the degree datum `D` is `1`. That degree is
`FiniteAbstractField.residueDegree` (M010.127, module
`Degree.Fields.FiniteAbstractField.Residue.Definitions`), which is the
`Nat.card` of the residue quotient `D.residueQuotient (baseField G)`.

Modifications by Worker 171: the source theorem is converted to
`def base_residueDegreeStatement (D : DegreeData G) : Prop := (FiniteAbstractField.base G).residueDegree D = 1`.
Proofs of the target are a separate proof task, so the source proof is omitted.
That proof applies `Subtype.ext`, casts to `Cardinal`, and uses
`FiniteResidueAbstractField.residueDegreeCardinal_eq_coe` and
`DegreeData.residueDegreeCardinal_baseField`. The source `@[simp]` attribute
belongs on the theorem, so it is omitted from this `Prop` definition. The
namespace is prefixed with `Langlands.NYLL`. The only import is the
residue-data module `Degree.Fields.FiniteAbstractField.Residue.Definitions`.
This unit is not in the original M010 list of Task 5955. It is added at the
request of the executor of Task 5905 (Worker 303), whose later proof needs
this target.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
