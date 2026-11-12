# Statement: the original-module comparison is an isomorphism

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, II.2.5, final paragraph of the proof of the
Theorem, printed p.40 / PDF p.46, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Starting from a nondegenerate `D(X)`-module `M` and its sheaf
`M(U) = χ_U · M`, the source states `M_c(X) = ⋃_U χ_U · M = M`, because `M` is
nondegenerate.

`ModuleComparisonIsIso` is the closed proposition: for every `X : Type` with
a topology satisfying `Langlands.Topology.IsLocallyProfinite X` (Hausdorff with a
compact open neighborhood basis), and every `M` in the published
`NondegenerateModuleCat.{0, 0}` of `PointwiseTestAlgebra.Carrier X`, the actual
comparison `ModuleProjectorComparison.moduleComparison hX M` is an isomorphism
in that category. Its target is
`(ProjectorVectorSheaf.functor hX ⋙ CompactSectionTestModule.compactSectionFunctor hX).obj M`.
The comparison sends `m` to the compactly supported global section of the
projector sheaf with components `χ_U · m` on compact opens `U`.

The source's identification is therefore asserted through this canonical
map, not through an arbitrary isomorphism. The universe is `Type`, as for
the published `CompactSupport`. This file states the proposition only. Its
proof is the obligation of a later `lean.proof@1` task. It needs injectivity
(`χ_K · m = m` for a compact open `K`, so the component at `K` recovers `m`).
It also needs surjectivity (a compactly supported section is determined by
its component on a compact open containing its support).

Worker 184 implements this statement for Task 5338.
