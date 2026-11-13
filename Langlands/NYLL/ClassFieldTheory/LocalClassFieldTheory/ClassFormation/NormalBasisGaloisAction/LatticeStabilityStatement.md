# NYLL Galois stability of normal-basis lattice dilates

Worker 197 adapts M145.004 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean`,
lines 98–118 (target at lines 98–103 and section variables at lines 92–94).
The readable pinned original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The supplemental registration is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
There is no applicable NYLL entry in the Library's `notes/errata/`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.galoisGroup_apply_mem_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice` | `Langlands.NYLL.LocalClassFieldTheory.galoisGroup_apply_mem_chosenBaseUniformizerPow_chosenNormalBasisIntegerLatticeStatement` |

The proposition retains the source assertion that a Galois automorphism sends
an element of the normal-basis lattice multiplied by the `n`th power of the
chosen base uniformizer into the same submodule. The objects are the published
`Langlands.NYLL.CyclicCohomology.chosenNormalBasisIntegerLattice` and
`Langlands.NYLL.CyclicCohomology.chosenBaseUniformizerPowSubmodule`, imported from
the focused `NormalBasisLattice.U002.Definitions` and
`NormalBasisLattice.U014.Definitions` modules under
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand`.
The automorphism is applied directly to the field element, exactly as in the
original target.

The effective universe is `u`. The full source telescope is bound explicitly
in order: `(K L : Type u)`, instances `[Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] [IsGalois K L] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`, explicit `(n : Nat)` and
`(sigma : Gal(L/K))`, implicit `{x : L}`, and the explicit membership proof
`hx`. The premise `hx` is retained even though the conclusion does not depend
on its proof term. The later source variables for a valuation on `L`, valuation
extension and integral closure begin at lines 120–122 and are absent here,
as in the original declaration.

Modifications are the `Langlands.NYLL` namespace prefix, `Statement` suffix,
replacement of the theorem and proof by a `Prop`-valued definition of its exact
target, and extraction into this focused pair. The focused imports replace the
broad original imports; unrelated declarations and unused namespace openings
are omitted. The unused-variable linter is disabled only for this declaration
to retain the source membership premise `hx` without a warning; this option
does not change the proposition. No proof of this target or new instance is
introduced. The source
copyright and author header is retained; the Apache-2.0 `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE` remain applicable. This supporting target proves no
class-formation or reciprocity theorem.
