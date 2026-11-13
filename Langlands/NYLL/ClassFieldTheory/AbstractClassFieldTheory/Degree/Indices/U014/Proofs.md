# NYLL M006.014: multiplication of cardinal relative indices

The paired Lean file proves
`Langlands.NYLL.ClassFormation.relativeIndexCardinal_mulStatement`,
imported from
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U012.Statements`.
The theorem is
`Langlands.NYLL.ClassFormation.relativeIndexCardinal_mul`.
Its type is exactly that named target applied to its source parameters.

The retained parameters, in order, are implicit `G : Type u`, the instance
`[Group G]`, implicit `M L K : Subgroup G`, explicit `hML : M ≤ L`,
and explicit `hLK : L ≤ K`. The conclusion is

```lean
relativeIndexCardinal hML * relativeIndexCardinal hLK =
  relativeIndexCardinal (hML.trans hLK)
```

Here each index is the cardinality of the actual left-coset type, in
`Cardinal.{u}`. The proof applies to infinite groups and infinite coset
spaces and requires no normality or finiteness premise.

The implementation first unfolds the named target. It commutes the two
cardinal factors and unfolds `relativeIndexCardinal` and
`intersectionIndexCardinal`. Rewriting with `Cardinal.mul_def` leaves
equality between the cardinality of
`(K ⧸ L.subgroupOf K) × (L ⧸ M.subgroupOf L)` and that of
`K ⧸ M.subgroupOf K`. Applying `Cardinal.mk_congr` to the inverse of
`Langlands.NYLL.Subgroup.quotientTowerEquiv hML hLK` proves that equality.
The initial commutation preserves the source's displayed factor order.

The direct imports are the published target module and
`Langlands.NYLL.GaloisCohomology.GroupTheory.QuotientTower`.
The cardinal-index data come through the target's import of
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U010.Definitions`.
The only additional substantive construction used by this proof is the
published quotient-tower equivalence, which reuses Mathlib's
`Subgroup.quotientEquivProdOfLE` and flattens the nested subgroup quotient.
The cardinal product and congruence laws are Mathlib results. No preceding
NYLL index theorem or host class-formation or reciprocity result is used.

The original is Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean`,
M006.014, lines 166–174 (signature 167–170); the cardinal data are
M006.010–011 at lines 131–141. The source was read through line 190,
including its header, section parameters, data and complete selected proof.
Its SHA-256 is
`da0a361d29cf76e77dd0556ca8384838b7231183333a68643acbd1021c95ad71`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and is readable at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean`.

Worker 183 extracted the focused proof, prefixed the namespace with
`Langlands.NYLL`, replaced the source import by the two published modules,
and changed the result type to the existing named target, unfolded at the
start of the proof. The remaining proof follows the source directly, with
the equivalence name fully qualified. The unused source section variable
`D : Type v` and `[Group D]` do not occur in the original elaborated
declaration and are omitted. The original target and all imported files
are unchanged. No applicable erratum was found in the project notes lookup.

The original copyright, Apache-2.0 release and author header are retained.
The unchanged attribution files are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
