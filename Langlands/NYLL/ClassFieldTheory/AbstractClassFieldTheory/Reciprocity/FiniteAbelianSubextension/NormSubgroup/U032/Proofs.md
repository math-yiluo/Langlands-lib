# NYLL M296.032: compositum norms lie in both norm subgroups

Worker 275, 16 November 2026.

## Source and attribution

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`,
M296.032, lines 451–459, with representation-section scaffolding at
lines 30–34 and 404–411. The source file has SHA-256
`f77cd402e62f7cd39a93a02269c2bfcffd9dc69b3919d352581a21d55aba67c0`.
The registered sources are
`external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.
The original copyright, Apache-2.0 license and author header are retained.
The applicable license and notices are already published in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

## Exact target and scope

The theorem
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.normSubgroup_compositum_le_inf`
proves the published proposition
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.normSubgroup_compositum_le_infStatement`
at the complete source telescope:

```lean
{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
{K : ClosedSubgroup G} (A : Rep ℤ G)
(L₁ L₂ : FiniteAbelianSubextension K)
```

Thus
`normSubgroup A (L₁.compositum L₂) ≤
normSubgroup A L₁ ⊓ normSubgroup A L₂`
inside `AddSubgroup (ambientFixedAddSubgroup A K)`. The acting group is in
universe zero through `IntegralRepGroupType`, as required by `Rep ℤ G`;
the representation carrier retains its free universe.
The compositum and norm subgroups are the published actual constructions.
The theorem has no topological-group, compactness or class-field-axiom
premise.

## Implemented proof

For an element of the compositum's norm subgroup, apply
`normSubgroup_antitone` to `le_compositum_left L₁ L₂` and
`le_compositum_right L₁ L₂`. These give membership in the left and right
norm subgroups. Their pair is membership in the intersection, so the
desired subgroup containment follows.

The proof consumes M296.031 from
`FiniteAbelianSubextension.NormSubgroup.U031.Proofs` and the two
compositum inclusions from `FiniteAbelianSubextension.M296018Proof` and
`FiniteAbelianSubextension.M296019Proof`, all under the common module
prefix
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity`.

## Modifications

The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
The source imports are replaced by the published target module and the
three prerequisite proof modules. The theorem's explicit conclusion is
written as the named target applied to the unchanged source arguments.
The proof body and theorem docstring are unchanged. Unrelated declarations,
the group-only section and the unused `universe u` are omitted; the
representation-section binders, opens and `noncomputable section` are
retained.
