# NYLL M010: finite relative residue and ramification targets

The source is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`
(file SHA-256 `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`).
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

All public names in the table use prefix
`Langlands.NYLL.ClassFormation.DegreeData.`, unless written in full.
Original names use prefix `ClassFormation.DegreeData.`.

| Unit | Original name | Source lines | Adapted name |
| --- | --- | --- | --- |
| M010.089 | `FiniteAbstractExtension.residueDegree_coe` | 755–761 | `FiniteAbstractExtension.residueDegree_coeStatement` |
| M010.090 | `FiniteAbstractExtension.ramificationIndex_coe` | 764–770 | `FiniteAbstractExtension.ramificationIndex_coeStatement` |
| M010.093 | `FiniteAbstractExtension.mapped_relIndex_eq_residueDegree` | 789–793 | `FiniteAbstractExtension.mapped_relIndex_eq_residueDegreeStatement` |
| M010.094 | `FiniteAbstractExtension.inertia_relIndex_eq_ramificationIndex` | 797–801 | `FiniteAbstractExtension.inertia_relIndex_eq_ramificationIndexStatement` |
| M010.095 | `FiniteAbstractExtension.degree_eq_residueDegree_mul_ramificationIndex` | 805–811 | `FiniteAbstractExtension.degree_eq_residueDegree_mul_ramificationIndexStatement` |
| M010.096 | `FiniteAbstractExtension.ramificationIndex_eq_one_of_isUnramified` | 814–820 | `FiniteAbstractExtension.ramificationIndex_eq_one_of_isUnramifiedStatement` |
| M010.097 | `FiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified` | 823–828 | `FiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamifiedStatement` |
| M010.100 | `FiniteAbstractExtension.residueDegree_eq_degree_of_isUnramified` | 851–855 | `FiniteAbstractExtension.residueDegree_eq_degree_of_isUnramifiedStatement` |
| M010.103 | `FiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe` | 880–891 | `FiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coeStatement` |

Each target keeps implicit `{G : Type u} [Group G]
[TopologicalSpace G]`, explicit `(E : FiniteAbstractExtension G)`, then
explicit `(D : DegreeData G)`. M010.096 and M010.100 additionally keep
explicit `(hE : E.IsUnramified D)`; M010.097 keeps explicit
`(hE : E.IsTotallyRamified D)`. These source hypotheses remain proposition
parameters even though the equality bodies do not syntactically mention
the proof variables. No other hypothesis or instance parameter is added.

The two coercion targets equate the natural value of the positive residue
degree or ramification index with `Nat.card` of the exact mapped-subgroup
or inertia-intersection quotient. The two relative-index bridges use the
field subgroup inside the base subgroup, retaining that order after
mapping or intersecting with the degree kernel.

The finite fundamental identity states the natural equality of extension
degree with residue degree times ramification index, in that factor order.
Unramifiedness forces ramification index one, total ramification forces
residue degree one, and an unramified extension has residue degree equal to
extension degree. These are source theorem targets on the existing
structural ramification predicates. The final target equates the Type-zero
relative residue cardinal with the cardinal cast of the positive residue
degree's natural value.

The imported data retain the source positive `Nat.card` constructions and
actual finite quotient types. Worker 198 prefixes namespaces, narrows
imports and converts each source theorem to a Prop-valued definition
ending in `Statement`. Its body is the original proposition. Source proof
bodies and simp attributes are omitted; no theorem is proved here.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
