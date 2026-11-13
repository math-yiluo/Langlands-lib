# NYLL M010.027: the finite residue cardinal as a natural cardinal

This file proves `Langlands.NYLL.ClassFormation.DegreeData.FiniteResidueAbstractField.residueDegreeCardinal_eq_coeStatement`
with the source-adapted theorem `Langlands.NYLL.ClassFormation.DegreeData.FiniteResidueAbstractField.residueDegreeCardinal_eq_coe`.

Its parameters are implicit `G : Type u`, `[Group G]`,
`[TopologicalSpace G]`, implicit `D : DegreeData G`, and explicit
`K : FiniteResidueAbstractField D`. Its declared type is exactly
`residueDegreeCardinal_eq_coeStatement K`:
`D.residueDegreeCardinal K.field = ((K.residueDegree : ℕ) : Cardinal)`.
The residue quotient and this cardinal live in universe zero even for
arbitrary `G : Type u`.

The implementation follows M010.027, lines 206–212 (the next unit starts
at 223). A `change` step unfolds the named proposition, the absolute
residue cardinal, its relative-index definition, and the underlying natural
of `residueDegree`. This gives equality between
`Cardinal.mk (D.residueQuotient K.field)` and the cardinal cast of its
`Nat.card`. The reverse of Mathlib's `Nat.cast_card` proves that equality.
Its finite-type requirement is supplied by the published instance
`Langlands.NYLL.PortInternal.M010.d024 K`, whose value is the bundled
`K.finiteResidueQuotient`; there is no additional finite instance premise.

The sole direct import is `Fields.FiniteResidue.Statements`. The proof
uses its published finite-residue and initial field definitions and
Mathlib's `Nat.cast_card` from `Mathlib.SetTheory.Cardinal.Finite` at the
approved Mathlib pin `5ed2965256430c3649e86755f9576b54eca72435`.
It does not depend on the separately proved `residueDegree_coe`, since
the coercion reduces by definition. The original `change` and exact proof
are retained. The source's `simp` attribute is omitted; the theorem is
available for explicit application.

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`
(file SHA-256 `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`).
The readable original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The routing reference is `notes/reuse/nyll-public-port-plan.md`, with M010's
unit rows in `notes/reuse/nyll-public-port/m001-m024.md`.

Worker 188 extracts this focused proof, prefixes its namespace with
`Langlands.NYLL`, narrows the source imports to the published modules
listed above, and states the result using the exact published named target.
The original copyright, Apache-2.0 and author header is retained.
The unchanged attribution files are `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support theorem supplies no host class-formation, cup, transfer, Tate
or reciprocity result.
