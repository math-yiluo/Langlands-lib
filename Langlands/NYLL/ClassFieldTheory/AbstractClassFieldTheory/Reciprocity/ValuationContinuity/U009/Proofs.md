# NYLL M301.009: surjectivity of the unramified degree homomorphism

The theorem
`Langlands.NYLL.ClassFormation.DegreeData.unramifiedDegreeHom_surjective`
proves the unchanged published target
`Langlands.NYLL.ClassFormation.DegreeData.unramifiedDegreeHom_surjectiveStatement D K f hf`.
It retains the complete source telescope: implicit `{G : Type u}` for an
arbitrary universe `u`, `[Group G]`, `[TopologicalSpace G]`, followed by
explicit `(D : DegreeData G)`, `(K : FiniteResidueAbstractField D)`,
`(f : ℕ)` and `(hf : 0 < f)`. There is no `IsTopologicalGroup G` premise.

The target unfolds to
`Function.Surjective (unramifiedDegreeHom D K f hf)`.
The actual continuous homomorphism has domain `K.toSubgroup` and codomain
`Multiplicative (ZMod f)`. Its definition is
`(zHatReductionMul f hf).comp (D.normalizedDegree K)`: normalized degree
followed by reduction modulo the positive integer `f`.

## Implemented proof

For an arbitrary `z : Multiplicative (ZMod f)`, the published
`zHatReduction_surjective f hf z.toAdd` supplies `w : ZHat` whose
reduction is `z.toAdd`. The published
`D.normalizedDegree_surjective K (Multiplicative.ofAdd w)` then supplies
`k : K.toSubgroup` whose normalized degree is `Multiplicative.ofAdd w`
(`K.toSubgroup` is definitionally `K.field.toSubgroup`).

The witness for surjectivity is this `k`. `Multiplicative.ext` reduces
the required equality to the underlying additive values. Unfolding the
composed map by `change` gives
`zHatReduction f hf (D.normalizedDegree K k).toAdd = z.toAdd`.
Rewriting by the chosen normalized-degree equation leaves exactly the
reduction equation for `w`.

The three direct imports are the published target module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.Statements`,
the reduction proof module
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U008.Proofs`,
and the normalized-degree proof module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U009.Proofs`.
These imports supply the unchanged actual constructions and both
surjectivity results used in the proof.

## Source, modifications and attribution

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean>),
lines 128–141 (M301.009), with section parameters at lines 22–36.
The original file SHA-256 is
`29a3ec39fcabc17faa969f1c4c225a7cfd07555a00298e58daaa4b6fa6c7bb60`.
The source is registered as
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

Worker 226 extracts only M301.009, adds the `Langlands.NYLL` namespace
prefix, replaces the three broad source imports with the focused imports
above, and changes the theorem conclusion to the exact published Statement
applied to the same parameters. The source proof body, docstring, universe,
section variables, binder kinds and parameter order are unchanged. The
unused source openings are omitted. Worker 303 supplied the focused proof
route and its earlier development check in the task context and is credited
as coauthor.

The original copyright and author header is retained verbatim. The port
remains under Apache-2.0; the existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
This unit proves the stated surjectivity for the NYLL abstract degree datum.
