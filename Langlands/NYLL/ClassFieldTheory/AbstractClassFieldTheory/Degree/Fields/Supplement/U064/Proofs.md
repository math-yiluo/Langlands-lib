# NYLL M010.064: total ramification of a Galois subextension as image containment

This file proves `Langlands.NYLL.ClassFormation.DegreeData.GaloisSubextension.isTotallyRamified_iff_image_leStatement`
with the source-adapted theorem `Langlands.NYLL.ClassFormation.DegreeData.GaloisSubextension.isTotallyRamified_iff_image_le`.

Its parameters are implicit `G : Type u`, `[Group G]`,
`[TopologicalSpace G]`, implicit `K : ClosedSubgroup G`, explicit
`L : GaloisSubextension K`, then explicit `D : DegreeData G`. Its type is
exactly `isTotallyRamified_iff_image_leStatement L D`: `L.IsTotallyRamified D`
holds if and only if
`K.toSubgroup.map D.degree.toMonoidHom ≤
L.field.toSubgroup.map D.degree.toMonoidHom`, that is, the degree image of
the base subgroup `K` is contained in the degree image of the subgroup
`L.field` of the upper field. No finiteness, profiniteness or other
hypothesis is added; the normality bundled in `L` is not used.

## Proof

The proof is the source term
`L.toAbstractExtension.isTotallyRamified_iff_image_le D`, following
M010.064, lines 543–548 (the next unit starts at 556). It applies the
published M010.047 theorem
`Langlands.NYLL.ClassFormation.DegreeData.AbstractExtension.isTotallyRamified_iff_image_le`
to the underlying abstract extension `L.toAbstractExtension`. That theorem
has type `AbstractExtension.isTotallyRamified_iff_image_leStatement
L.toAbstractExtension D`, which Lean accepts at the target type by
definitional unfolding:

- `GaloisSubextension.IsTotallyRamified L D` is by definition
  `L.toAbstractExtension.IsTotallyRamified D`;
- the published `toAbstractExtension` has `field := L.field` and
  `base := K`, so the field and base subgroups of the underlying abstract
  extension reduce to `L.field` and `K`;
- both named statements unfold to the same `Iff` between
  `IsTotallyRamified` and the subgroup-image containment.

The source docstring "Total ramification is the canonical equality of
degree images" is retained verbatim. The proposition itself is a
containment; since `L.below : L.field.toSubgroup ≤ K.toSubgroup`, the
reverse containment of the images always holds, so the containment is
equivalent to equality of the two degree images, but the theorem states
only the containment.

## Dependencies

The direct imports are
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Supplement.TotalRamificationStatements`,
which supplies the target statement together with the published
`GaloisSubextension` definitions (`toAbstractExtension`,
`IsTotallyRamified`), and
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.U047.Proofs`,
which supplies the published M010.047 theorem used by the source proof.
No other theorem is used, and no published Lean/Markdown pair is changed.
Kernel axioms reported for the theorem are `propext`,
`Classical.choice` and `Quot.sound` (entering through the Mathlib
definitions in the statement).

## Source and modification record

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`
(file SHA-256 `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`),
theorem `ClassFormation.DegreeData.GaloisSubextension.isTotallyRamified_iff_image_le`,
lines 543–548. The readable original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The routing reference is `notes/reuse/nyll-public-port-plan.md`, with M010's
unit rows in `notes/reuse/nyll-public-port/m001-m024.md`.

Worker 79 extracts this focused proof, prefixes its namespace with
`Langlands.NYLL`, replaces the whole-file source imports by the two
published modules listed above, and states the result using the exact
published named target instead of the inline source proposition. The
original proof term, parameter order and scope are retained. The original
copyright, Apache-2.0 and author header is retained. The unchanged
attribution files are `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support theorem supplies no host class-formation, cup, transfer, Tate
or reciprocity result.
