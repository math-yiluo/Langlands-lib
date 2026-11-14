# NYLL M296.020: compositum below a common upper bound

Worker 663, 14 November 2026.

This module proves
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.compositum_leStatement`
by the theorem
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.compositum_le`.
The statement and its data are imported from the published module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.OrderStatements`.

## Source and attribution

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`,
M296.020, lines 267–271. The section context is at lines 30–52.
The source file has SHA-256
`f77cd402e62f7cd39a93a02269c2bfcffd9dc69b3919d352581a21d55aba67c0`.
It is available under the registered source
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The original copyright, authors and Apache-2.0 header are retained.
The Library already carries `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.

## Exact telescope and conclusion

The theorem preserves the source universe `u`, implicit `{G : Type u}`,
instances `[Group G]` and `[TopologicalSpace G]`, implicit
`{K : ClosedSubgroup G}`, and implicit
`{L₁ L₂ P : FiniteAbelianSubextension K}`. Its containment hypotheses
`(h₁ : L₁ ≤ P)` and `(h₂ : L₂ ≤ P)` are explicit arguments.
The theorem's type is exactly `compositum_leStatement h₁ h₂` applied to
these same parameters. Unfolding the target gives `L₁.compositum L₂ ≤ P`.
No topological group assumption is added.

## Implemented proof

The order on finite abelian subextensions reverses inclusion of their
closed subgroups. Thus `h₁` and `h₂` respectively send membership in
`P.field` to membership in `L₁.field` and `L₂.field`. The compositum's
closed subgroup is definitionally `L₁.field ⊓ L₂.field`. The proof takes
an element and its membership proof `hp` in `P.field`, and returns
`⟨h₁ hp, h₂ hp⟩`, its membership in this intersection.

The implemented term `fun _ hp => ⟨h₁ hp, h₂ hp⟩` is unchanged from the
pinned source. It proves the common-upper-bound clause; the two inclusions
of the factors into the compositum are separate published targets and are
not additional claims of this module.

## Modifications

1. The namespace `ClassFormation` is prefixed by `Langlands.NYLL`.
2. The original imports are replaced by the published `OrderStatements`
   module, which supplies the fixed target, order and compositum.
3. The source conclusion `L₁.compositum L₂ ≤ P` is expressed by the
   definitionally equal target `compositum_leStatement h₁ h₂`.
4. Only M296.020 is extracted into `FiniteAbelianSubextension/U020/Proofs`.
   The unused `noncomputable section` and
   `open CyclicCohomology KummerTheory` are omitted, and a module
   modification note is added. The theorem's docstring, telescope and
   proof term are preserved.
