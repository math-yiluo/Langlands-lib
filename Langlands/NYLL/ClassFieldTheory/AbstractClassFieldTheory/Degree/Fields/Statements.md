# NYLL M010: initial field, inertia and residue targets

These nine Prop-valued targets extract signatures from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`, pinned
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The file SHA-256 is
`841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

The prefix for all names is `Langlands.NYLL.ClassFormation`. The imported
`Fields.Definitions` supplies the actual source data: arbitrary topologized
groups, continuous surjective degree maps to the Type-zero NYLL closure model,
closed field subgroups and inertia kernels, and actual residue coset types
and cardinalities. The targets keep these objects and their canonical instances.

| Unit | Source signature lines and name after `ClassFormation.` | Target name after the same prefix |
| --- | --- | --- |
| M010.004 | 56–57, `baseField_toSubgroup` | `baseField_toSubgroupStatement` |
| M010.005 | 61–62, `le_baseField` | `le_baseFieldStatement` |
| M010.007 | 76–77, `DegreeData.mem_inertia_iff` | `DegreeData.mem_inertia_iffStatement` |
| M010.009 | 88–89, `DegreeData.restrictedDegree_apply` | `DegreeData.restrictedDegree_applyStatement` |
| M010.011 | 97–98, `DegreeData.fieldImage_eq_map` | `DegreeData.fieldImage_eq_mapStatement` |
| M010.013 | 112–113, `DegreeData.mem_fieldInertia_iff` | `DegreeData.mem_fieldInertia_iffStatement` |
| M010.016 | 129–130, `DegreeData.mem_fieldInertiaWithin_iff` | `DegreeData.mem_fieldInertiaWithin_iffStatement` |
| M010.019 | 145–147, `DegreeData.residueDegreeCardinal_eq_mk_residueQuotient` | `DegreeData.residueDegreeCardinal_eq_mk_residueQuotientStatement` |
| M010.020 | 152–153, `DegreeData.residueDegreeCardinal_baseField` | `DegreeData.residueDegreeCardinal_baseFieldStatement` |

Except for M010.004, the source section supplies implicit `G : Type u`,
`[Group G]` and `[TopologicalSpace G]`. M010.004 has explicit `G` followed by
these same instances. M010.005 then has explicit `K : ClosedSubgroup G` and
asserts its inclusion in the underlying subgroup of `baseField G`.
All `DegreeData` targets have explicit `D`; all but M010.007 and M010.020
then have explicit `K`. M010.007 has explicit `g : G`; M010.009 and M010.016
have explicit `k : K.toSubgroup`; M010.013 has explicit `g : G` after `K`.
M010.020 has only `D` after the implicit group and topology parameters.
No compactness, topological-group, finiteness or extra normality hypothesis
is introduced. In particular no finite-residue structure is needed.

The underlying-subgroup, membership and evaluation assertions are the actual
equalities, inclusions and equivalences shown in Lean. The field-image target
relates the restricted range to the map of the underlying subgroup. The last
two assertions use genuine coset cardinalities: one identifies the residue
cardinal with `Cardinal.mk` of the residue coset type, and the other asserts
that the base field has residue cardinal one. Surjectivity belongs to the
original `DegreeData` structure and remains available as its field, rather
than being a new assumption inserted into these conclusions.

Worker 120 prefixes the namespace, appends `Statement` to theorem names,
replaces their proof bodies by proposition definitions, omits theorem-only
simp attributes, and retains the source universe and noncomputable section.
The single focused data import suffices to state these propositions; no
source theorem proof is imported. These are targets only. No proof or later
finite-residue field/extension result, normalized degree, arithmetic degree
construction, host comparison or reciprocity statement is supplied.

The original copyright, Apache-2.0 and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
