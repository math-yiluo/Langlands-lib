# NYLL M166.001: relative norms along equal closed subgroups agree (proof)

This module proves the published target
`Langlands.NYLL.LocalClassFieldTheory.relativeNorm_coe_eq_of_closedSubgroup_eqStatement`
([target](Statements.md), NYLL source unit M166.001) by the theorem

```lean
theorem relativeNorm_coe_eq_of_closedSubgroup_eq
    {G : Type} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G)
    (B B' C C' : ClosedSubgroup G)
    (hCB : C.toSubgroup ≤ B.toSubgroup)
    (hC'B' : C'.toSubgroup ≤ B'.toSubgroup)
    [hfinite : Finite
      (B.toSubgroup ⧸ extensionSubgroup B C hCB)]
    [hfinite' : Finite
      (B'.toSubgroup ⧸ extensionSubgroup B' C' hC'B')]
    (hB : B = B') (hC : C = C')
    (x : ambientFixedAddSubgroup A C)
    (x' : ambientFixedAddSubgroup A C')
    (hx : x.1 = x'.1) :
    relativeNorm_coe_eq_of_closedSubgroup_eqStatement A B B' C C' hCB hC'B'
      hB hC x x' hx
```

in namespace `Langlands.NYLL.LocalClassFieldTheory`, the adapted source name.
Its binders are those of the target, with the same names, in the same order
and with the same binder kinds, and its type is the target applied to them.
Like the target, it has exactly one universe parameter, `u_1`, the universe
of the carrier of `A`.

The theorem says the following. Let `A` be an integral representation of a
topological group `G`. Let `C ≤ B` and `C' ≤ B'` be closed subgroups with
finitely many left cosets, and let `x` be a `C`-fixed and `x'` a `C'`-fixed
element of `A`. If `B = B'`, `C = C'` and `x` and `x'` have the same
underlying element of `A`, then the published relative norms
`relativeNorm A B C hCB x` and `relativeNorm A B' C' hC'B' x'` have the same
underlying element of `A`.

## Proof

The proof is the source tactic proof, preceded by one added line that
unfolds the target:

```lean
  unfold relativeNorm_coe_eq_of_closedSubgroup_eqStatement
  subst B'
  subst C'
  have hle : hCB = hC'B' := Subsingleton.elim _ _
  subst hC'B'
  have hfin : hfinite = hfinite' := Subsingleton.elim _ _
  subst hfinite'
  have hxx' : x = x' := Subtype.ext hx
  subst x'
  rfl
```

1. `unfold` replaces the target `def` by its body, the equation in `A.V`
   between the two coerced relative norms. After it, the remaining steps
   act on exactly the goal of the source theorem.
2. `subst B'` and `subst C'` use `hB : B = B'` and `hC : C = C'` to replace
   `B'` by `B` and `C'` by `C` everywhere, including in the types of
   `hC'B'`, `hfinite'` and `x'`.
3. Both containment proofs now have the type `C.toSubgroup ≤ B.toSubgroup`,
   a proposition, so `Subsingleton.elim` proves `hCB = hC'B'`, and `subst`
   replaces `hC'B'` by `hCB`.
4. The two finiteness instances now have the same type, a `Finite`
   statement, which is a proposition. Again `Subsingleton.elim` proves them
   equal and `subst` replaces `hfinite'` by `hfinite`.
5. `x` and `x'` now lie in the same subtype
   `ambientFixedAddSubgroup A C`. Mathlib's `Subtype.ext` turns
   `hx : x.1 = x'.1` into `x = x'`, and `subst` replaces `x'` by `x`.
6. The two sides of the goal are now the same term, and `rfl` closes it.

## Dependencies

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldNorm.U001.Statements`
  is the published target, and the only import. Through it come
  `relativeNorm` (`Langlands.NYLL.ClassFormation.relativeNorm`),
  `ambientFixedAddSubgroup` (`Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup`)
  and `extensionSubgroup` (`Langlands.NYLL.CyclicCohomology.extensionSubgroup`).
- From Lean and Mathlib: the tactics `unfold` and `subst`, and the lemmas
  `Subsingleton.elim` and `Subtype.ext`.

No property of `relativeNorm` is used; the proof only identifies its
arguments. No other Library result and no helper declaration is used. The
published target and definitions are used by name and none of them is
modified. The module opens `CyclicCohomology`, `KummerTheory` and
`ClassFormation`, as the target module does, so that `extensionSubgroup` and
`ambientFixedAddSubgroup` in the binders resolve to the published names.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module
with zero errors and zero warnings. Inspection of the theorem reported kind
`theorem`, the single level parameter `u_1`, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`. This development check is not
acceptance.

## Source correspondence and modification record

The original declaration is the theorem
`LocalClassFieldTheory.relativeNorm_coe_eq_of_closedSubgroup_eq` in Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldNorm.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldNorm.lean#L34-L63)
(SHA-256 `f4529e6c10db2c36c8c1dd88506cb999bd030618c1800f1d1ab96ab604e5f4fd`).
Its docstring is at lines 34–37, its statement at lines 38–54 and its proof at
lines 55–63. The file-level section variables `K`, `Ω` (lines 31–32) occur
neither in its binders nor in its type, so the source theorem does not take
them.

| Original declaration | Adapted declaration |
| --- | --- |
| `theorem LocalClassFieldTheory.relativeNorm_coe_eq_of_closedSubgroup_eq` (M166.001) | `theorem Langlands.NYLL.LocalClassFieldTheory.relativeNorm_coe_eq_of_closedSubgroup_eq` (this module) |
| `ClassFormation.relativeNorm` (M024.009, in the statement) | `Langlands.NYLL.ClassFormation.relativeNorm` (published) |
| `KummerTheory.ambientFixedAddSubgroup` (M023.001, in the statement) | `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` (published) |
| `CyclicCohomology.extensionSubgroup` (M004.002, in the statement) | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (published) |

Worker 368 made these changes on 15 November 2026:

- the conclusion is written as the target applied to the theorem's binders,
  which are the source binders unchanged; the line
  `unfold relativeNorm_coe_eq_of_closedSubgroup_eqStatement` is added at the
  start of the proof, as explained above;
- the namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`;
- the source imports are replaced by the published target module. Of the
  source's opens, `CyclicCohomology`, `KummerTheory` and `ClassFormation` are
  kept, as in the target module; `RamificationTheory`, `LocalFieldTheory`,
  scoped `ValuativeRel`, the `noncomputable section` and the section
  variables are omitted;
- the docstring and the rest of the tactic proof are the source's,
  unchanged.

The registered source is `external-lean-reuse-snapshots-2026-10-21`
(fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`); the
attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The Lean
file keeps the original copyright and author header verbatim and records the
modifications. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are
unchanged in the Library. This support proof discharges no host
class-formation, cohomology or reciprocity target.
