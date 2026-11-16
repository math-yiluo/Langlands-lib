# NYLL M075.014: comparison of finite norm subgroups in a tower

`Langlands.NYLL.ClassFormation.abstractReciprocity_finiteNormSubgroup_le` proves
the published proposition
`Langlands.NYLL.ClassFormation.abstractReciprocity_finiteNormSubgroup_leStatement`
of module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.NormSubgroup.Statements`.

## Statement

The parameters are, in order, the section variables implicit
`G : IntegralRepGroupType` with instances `[Group G]` and `[TopologicalSpace G]`,
then explicit `A : Rep ℤ G`, explicit `K M L : ClosedSubgroup G`, explicit
`hLM : L.toSubgroup ≤ M.toSubgroup` and `hMK : M.toSubgroup ≤ K.toSubgroup`,
and the three instance arguments

```lean
[hKMfinite : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup)]
[hMLfinite : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup)]
[hKLfinite : Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
```

written, exactly as in the published statement, through the
`Subgroup.subgroupOf` bodies of the source's `extensionSubgroup` quotients. The
type of the theorem is exactly
`abstractReciprocity_finiteNormSubgroup_leStatement A K M L hLM hMK`, which
unfolds to

```lean
finiteNormSubgroup A K L (hLM.trans hMK) ≤ finiteNormSubgroup A K M hMK
```

Here the published `finiteNormSubgroup A K L h` (M039.001, module
`...Reciprocity.Construction.FiniteNormQuotient.Definitions`) is the range
`(relativeNorm A K L h).range` of the relative norm homomorphism
`A_L → A_K`, an additive subgroup of the `G_K`-fixed submodule
`ambientFixedAddSubgroup A K`. In words: for closed subgroups
`G_L ≤ G_M ≤ G_K` with finite quotients `G_K / G_M`, `G_M / G_L` and
`G_K / G_L`, every norm from `A_L` to `A_K` is a norm from `A_M` to `A_K`, that
is, `N_{L/K} A_L ⊆ N_{M/K} A_M`. The instance `hKLfinite` is used by the left
side, `hKMfinite` by the right side; `hMLfinite` is used only by the proof.

## Implemented proof

The module contains the single theorem
`abstractReciprocity_finiteNormSubgroup_le`. Its proof is:

1. `show finiteNormSubgroup A K L (hLM.trans hMK) ≤ finiteNormSubgroup A K M
   hMK` unfolds the published statement definition to the source statement.
2. `let T : DegreeData.FiniteTower G` builds the finite tower with
   `top := L`, `middle := M`, `base := K`, `top_le_middle := hLM`,
   `middle_le_base := hMK`, `finiteTopQuotient := hMLfinite` and
   `finiteBaseQuotient := hKMfinite` (the published structure
   `DegreeData.FiniteTower`, which extends `AbstractExtension.Tower`).
3. `rintro _ ⟨a, rfl⟩` introduces an element of the left side as
   `relativeNorm A K L (hLM.trans hMK) a` for some `a : ambientFixedAddSubgroup
   A L`, by the definitional description of membership in a homomorphism range.
4. `refine ⟨relativeNorm A M L hLM a, ?_⟩` gives the witness of membership in
   the right side, leaving the goal
   `relativeNorm A K M hMK (relativeNorm A M L hLM a) =
   relativeNorm A K L (hLM.trans hMK) a`.
5. `exact T.norm_trans_apply A a` closes it by the published norm transitivity
   `DegreeData.FiniteTower.norm_trans_apply` (M026.019). Its statement
   mentions `T.base`, `T.middle`, `T.top` and the tower inequalities, which
   reduce to `K`, `M`, `L`, `hMK`, `hLM` because `T` is a `let`-bound
   structure literal. The finiteness instances it uses are the tower instances
   `topQuotientFinite T` and `baseQuotientFinite T`, which are `hMLfinite` and
   `hKMfinite`, and the composite instance
   `DegreeData.FiniteTower.totalQuotientFinite T`; the last and the target's
   `hKLfinite` are proofs of the same proposition
   `Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)`, so they
   agree by proof irrelevance.

Imports: the required statement module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.NormSubgroup.Statements`
and the published proof module of `DegreeData.FiniteTower.norm_trans_apply`,
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.RelativeNorm.U019.Proofs`.
The other published declarations used are `finiteNormSubgroup`,
`relativeNorm`, `ambientFixedAddSubgroup`, `DegreeData.FiniteTower` and its
instances `topQuotientFinite`, `baseQuotientFinite` and `totalQuotientFinite`.
The kernel axioms reported by inspection are `propext`, `Classical.choice` and
`Quot.sound`.

## Source correspondence and modifications

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, pinned
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean`, SHA-256
`0fc1bd5c66d628b74e079fd54af4a9df7334343e38186983257da5ce6a8f06fb`, retained
under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Its registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Source name | Source lines | Port |
| --- | --- | --- | --- |
| M075.014 | `ClassFormation.abstractReciprocity_finiteNormSubgroup_le` | docstring 654–655, statement 656–667, proof 668–678 | the target theorem |

The enclosing source context is `namespace ClassFormation` (line 24),
`open KummerTheory` (26), `open CyclicCohomology` (28), the outer
`noncomputable section` (32) with `open CategoryTheory` (34) and the variable
lines 37–38, and the nested `noncomputable section` (451) with the variable
line 454, which redeclares `G` with the same binders; both sections close at
lines 1268–1269. The port keeps `namespace`, the two `open` lines, one
`noncomputable section` and the variable line for `G` under the namespace
prefix `Langlands.NYLL`. It omits `open CategoryTheory` and the outer variables
`{D : DegreeData G} {A : Rep ℤ G}` of line 38, which this theorem does not use
(it binds its own explicit `A`).

Modifications, all by Worker 735:

- The namespace is prefixed with `Langlands.NYLL`; the source imports are
  replaced by the two published modules listed above.
- The three finiteness binders are written through the `Subgroup.subgroupOf`
  bodies `M.toSubgroup.subgroupOf K.toSubgroup`,
  `L.toSubgroup.subgroupOf M.toSubgroup` and
  `L.toSubgroup.subgroupOf K.toSubgroup` of the source's
  `extensionSubgroup K M hMK`, `extensionSubgroup M L hLM` and
  `extensionSubgroup K L (hLM.trans hMK)`, as in the published statement;
  `extensionSubgroup` is the published `abbrev` for these terms.
- The conclusion is written as the published
  `abstractReciprocity_finiteNormSubgroup_leStatement A K M L hLM hMK`, and the
  proof begins with the `show` of step 1. The source proof steps (steps 2–5)
  are unchanged, and the theorem docstring is the source one.

This is an inclusion of norm subgroups in the NYLL abstract-field model. It
discharges no host class-formation, cup, transfer, Tate or reciprocity target.

## Attribution

The original copyright, author and Apache-2.0 header is retained verbatim, and
the Lean module docstring records the modifications. The existing Library files
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are preserved unchanged; their
SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
