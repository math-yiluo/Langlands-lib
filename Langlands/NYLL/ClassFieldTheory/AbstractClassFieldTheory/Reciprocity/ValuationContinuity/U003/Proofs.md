# NYLL M301.003: the defining unramified degree kernel equation

Worker 209 supplies the exact proof of the published target
`Langlands.NYLL.ClassFormation.DegreeData.unramifiedDegreeKernelWithin_eq_kerStatement`
in the imported `ValuationContinuity.Statements` module. The theorem is
`Langlands.NYLL.ClassFormation.DegreeData.unramifiedDegreeKernelWithin_eq_ker`.

Its complete telescope is implicit `{G : Type u}` for arbitrary universe
`u`, instance parameters `[Group G]` and `[TopologicalSpace G]`, then explicit
`(D : DegreeData G)`, `(K : FiniteResidueAbstractField D)`, `(f : ℕ)` and
`(hf : 0 < f)`, in that order. There is no `IsTopologicalGroup G` hypothesis.
The theorem's type is exactly the target applied to `D K f hf`, asserting

```lean
unramifiedDegreeKernelWithin D K f hf =
  (unramifiedDegreeHom D K f hf).toMonoidHom.ker
```

This is equality of subgroups of `K.toSubgroup`. The continuous
homomorphism `unramifiedDegreeHom D K f hf` reduces the normalized degree
modulo the positive integer `f`, with codomain `Multiplicative (ZMod f)`.
Both the homomorphism and the kernel subgroup are imported published
definitions, without modifications.

The implemented proof is `rfl`. Unfolding the target gives the displayed
equality, and `unramifiedDegreeKernelWithin` is defined to be its right
side. Reflexivity therefore proves the equality by definitional reduction.
This proof adds no assumptions, instances or attributes.

The source is Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`, commit `fbd320cd8b1b06487c58227e92eb135794267709`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean#L50-L55),
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean`,
M301.003, lines 50–55, with section parameters at lines 22–36. The full
source file has SHA-256
`29a3ec39fcabc17faa969f1c4c225a7cfd07555a00298e58daaa4b6fa6c7bb60`.
The readable pinned snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source identifiers are
`external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

Worker 209 extracts only this theorem, prefixes its namespace with
`Langlands.NYLL`, replaces the broad source imports with the published
target module, makes the inherited parameters explicit in the declaration,
and writes the theorem's type using the target. The source docstring and
`by rfl` proof are retained. The source's unused namespace openings are
omitted. The existing target and its dependencies are unchanged.

The original copyright and author header is retained. This adaptation is
under Apache-2.0; the applicable `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are already published in the Library.
