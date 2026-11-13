# NYLL M010: positive relative residue and ramification data

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
| M010.083 | `FiniteAbstractExtension.residueQuotientFinite` | 701–712 | `FiniteAbstractExtension.residueQuotientFinite` |
| M010.084 | `FiniteAbstractExtension.ramificationQuotientFinite` | 714–724 | `FiniteAbstractExtension.ramificationQuotientFinite` |
| M010.086 | `FiniteAbstractExtension.residueDegree` | 733–739 | `FiniteAbstractExtension.residueDegree` |
| M010.087 | `FiniteAbstractExtension.ramificationIndex` | 741–747 | `FiniteAbstractExtension.ramificationIndex` |

All four commands keep implicit `{G : Type u} [Group G]
[TopologicalSpace G]`, explicit `(E : FiniteAbstractExtension G)`, and then
explicit `(D : DegreeData G)`. The two instances are necessary additional
same-module dependencies M010.083/.084 of the requested positive numerical
invariants. They expose finiteness of the actual mapped-subgroup and
inertia-intersection coset types, respectively. They keep the source
registration scope and introduce no additional instance.

Their proof bodies retain `Cardinal.lt_aleph0_iff_finite.mp` followed by
unfolding the exact cardinal-index definitions. The only proof-name
substitution is from the original private
`E.relativeResidueDegreeCardinal_lt_aleph0 D` and
`E.relativeRamificationIndexCardinal_lt_aleph0 D` to the separately published
proofs `Langlands.NYLL.PortInternal.M010.d081 E D` and
`Langlands.NYLL.PortInternal.M010.d082 E D`. Those are proofs of the
source-exact M010.081/.082 targets, whose names are stabilized by the port.
The `simpa` lists also unfold `d081Statement` and `d082Statement`,
respectively, to expose the propositions proved by those imported results.
The cardinal fundamental identity supplies the finiteness route through
those proofs. No cardinal inequality is added as a parameter.

The two positive invariants preserve their exact source construction:
each is `Nat.card` of its actual relative coset type, paired with
`Nat.card_pos`. The quotient types are nonempty, and the two source finite
instances supply their finiteness. The result type is `ℕ+`; these data do
not define an invariant by a natural index that becomes zero in the
infinite case.

Worker 198 prefixes namespaces, narrows imports, and substitutes the stable
published proof names as recorded above. All source quotient expressions,
data constructor fields and positivity proof terms are retained. The
separate statement module records the source theorem targets.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
