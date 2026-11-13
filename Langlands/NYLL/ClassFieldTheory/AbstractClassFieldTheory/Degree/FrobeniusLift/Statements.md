# NYLL M012: positive representatives and restriction evaluation targets

These two proposition definitions adapt theorem signatures from Naganori
Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusLift.lean`.
Its SHA-256 is
`a0b7ac8afcc55cad383a16e6dfe093e147770a7e8f5d21c3f8843744b57b7061`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

The original names have prefix `ClassFormation`; adapted names have prefix
`Langlands.NYLL.ClassFormation`.

| Unit | Source signature lines | Original suffix | Adapted suffix |
| --- | --- | --- | --- |
| M012.001 | 31–33 | `exists_positive_nsmul_one_sub_mem_of_index_ne_zero` | `exists_positive_nsmul_one_sub_mem_of_index_ne_zeroStatement` |
| M012.008 | 120–125 | `DegreeData.extensionRestriction_mk` | `DegreeData.extensionRestriction_mkStatement` |

M012.001 retains the explicit binders `H : AddSubgroup ZHat`,
`hH : H.index ≠ 0`, then `z : ZHat`. The hypothesis remains an explicit
parameter of the target even though its body does not reference that proof.
Its body is exactly `∃ n : ℕ, 0 < n ∧ z - n • (1 : ZHat) ∈ H`.
In particular, positivity is strict and uses natural scalar multiplication;
the target does not replace `0 < n` with a nonnegativity condition. `ZHat`
is the published Type-zero source closure model, rather than a replacement
profinite-integer model. The source section's group parameters do not occur
in this theorem and therefore are not parameters of either original theorem
or adapted definition.

M012.008 retains universe `u`, implicit `G : Type u`, then `[Group G]`
and `[TopologicalSpace G]`. The explicit binders are `D : DegreeData G`,
`K L : ClosedSubgroup G`, `hLK : L.toSubgroup ≤ K.toSubgroup`, followed
by instance binder
`[hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]`,
then explicit `k : K.toSubgroup`. Its body is the actual equality
`D.extensionRestriction K L hLK (QuotientGroup.mk k) = QuotientGroup.mk k`.
The left quotient is by extension inertia and the right quotient is by the
extension subgroup, as in the source. No finite-residue, finiteness,
profinite-group or topological-group premise is added.

As in the accompanying data unit, the source abbreviation
`CyclicCohomology.extensionSubgroup K L hLK` is expanded to its exact
Mathlib body `L.toSubgroup.subgroupOf K.toSubgroup`. Its original definition
is M004.002 at `Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`,
lines 47–54, file SHA-256
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`.
The explicit containment binder and normality binder are preserved.
The imported `FrobeniusLift.Definitions` contains the source-preserving
M012.002, .003 and .007 constructions on the published degree data.

Worker 191 prefixes the namespace, appends `Statement`, changes theorem
commands into Prop-valued definitions and omits the theorem proof bodies.
The source `[simp]` attribute on M012.008 is omitted because this is a
proposition definition rather than a proof of a rewrite rule. The original
docstrings are replaced with target descriptions. The source noncomputable
section and universe/section declarations are retained. The full
`Degree.Frobenius` import and unused `open CyclicCohomology` are replaced
by the focused data import. Apart from that import reduction, namespace
adaptation and abbreviation expansion, the source statements and complete
binder order are unchanged.

These are unproved theorem targets. Neither source theorem proof, the other
M012 normalized-degree/Frobenius declarations, nor any host reciprocity
comparison is supplied.

The original copyright, author and Apache-2.0 header is retained.
`licenses/NYLL/LICENSE` has SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`;
`licenses/NYLL/NOTICE` has SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
