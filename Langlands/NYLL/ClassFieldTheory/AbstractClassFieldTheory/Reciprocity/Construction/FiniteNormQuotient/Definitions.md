# NYLL M039: the finite norm quotient — data

The paired Lean file adapts six data definitions and one instance from
Naganori Yamaguchi's ClassFieldTheory at pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`,
SHA-256
`f541cbe9d1f0a01b867d7339fc7ef0eb830bd9bf799ceaadfb6506c4bb334da7`.
The source is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Its registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the available project notes.

## Source correspondence

Every original name has prefix `ClassFormation.` and every adapted name has
prefix `Langlands.NYLL.ClassFormation.`; the names are otherwise unchanged.

| Unit | Source name | Kind | Source lines (docstring–end) | Adapted name |
| --- | --- | --- | --- | --- |
| M039.001 | `finiteNormSubgroup` | def | 35–40 | `finiteNormSubgroup` |
| M039.002 | `FiniteNormQuotient` | def | 42–50 | `FiniteNormQuotient` |
| M039.003 | `finiteNormQuotientAddCommGroup` | instance | 52–61 | `finiteNormQuotientAddCommGroup` |
| M039.004 | `finiteNormQuotientConcreteEquiv` | def | 63–73 | `finiteNormQuotientConcreteEquiv` |
| M039.005 | `finiteNormClassHom` | def | 75–82 | `finiteNormClassHom` |
| M039.006 | `finiteNormClass` | def | 84–91 | `finiteNormClass` |
| M039.015 | `finiteNormQuotientLift` | def | 184–194 | `finiteNormQuotientLift` |

The enclosing source context is `universe u` (line 18, used only by the later
`finiteIntermediateField` section), `namespace ClassFormation` (line 20),
`open KummerTheory` (line 22), `open CyclicCohomology` (line 24),
`noncomputable section` (line 28), `section finiteNorms` (line 30) and the
group variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
(line 33). All source docstrings are retained verbatim. M039.015 follows the
theorems M039.007–M039.014 in the source; it depends on none of them and is
placed after M039.006 here. The theorem statements are in
[`Statements.md`](Statements.md).

## Objects and complete telescopes

Every declaration begins with implicit `{G : IntegralRepGroupType}`,
`[Group G]` and `[TopologicalSpace G]`; `Langlands.NYLL.IntegralRepGroupType`
is `Type 0`, and the representation carrier has an arbitrary universe. The
common data telescope then is, explicitly and in order, `A : Rep ℤ G`,
`K L : ClosedSubgroup G`, `hLK : L.toSubgroup ≤ K.toSubgroup`, followed by
the instance argument
`[Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]`.
There is no normality, topological-group or continuity assumption.

- `finiteNormSubgroup A K L hLK : AddSubgroup (ambientFixedAddSubgroup A K)`
  is `(relativeNorm A K L hLK).range`, the image `N_{L|K} A_L` of the
  published coset-sum norm `relativeNorm` (M024.009) in the fixed module
  `A_K`.
- `FiniteNormQuotient A K L hLK` is the type
  `ambientFixedAddSubgroup A K ⧸ finiteNormSubgroup A K L hLK`, Mathlib's
  quotient of the additive group `A_K` by that subgroup. As in the source it is
  a plain (semireducible) `def`, not an `abbrev`; its universe is the carrier
  universe.
- `finiteNormQuotientAddCommGroup` is an `instance` of
  `AddCommGroup (FiniteNormQuotient A K L hLK)` with source body
  `unfold FiniteNormQuotient; infer_instance`, i.e. Mathlib's quotient
  additive group structure. It is a global instance in
  `Langlands.NYLL.ClassFormation`, exactly as in the source scope. Its class
  argument is the new type `FiniteNormQuotient`, which no Mathlib or Library
  instance targets, so it introduces no conflicting instance.
- `finiteNormQuotientConcreteEquiv` is
  `FiniteNormQuotient A K L hLK ≃+ ambientFixedAddSubgroup A K ⧸ finiteNormSubgroup A K L hLK`,
  with source body `unfold FiniteNormQuotient; exact AddEquiv.refl _`.
- `finiteNormClassHom` is
  `ambientFixedAddSubgroup A K →+ FiniteNormQuotient A K L hLK`, with source
  body `unfold FiniteNormQuotient; exact QuotientAddGroup.mk' (finiteNormSubgroup A K L hLK)`,
  the canonical projection.
- `finiteNormClass` takes in addition explicit
  `a : ambientFixedAddSubgroup A K` and returns
  `finiteNormClassHom A K L hLK a : FiniteNormQuotient A K L hLK`.
- `finiteNormQuotientLift` has the source telescope
  `{B : Type*} [AddCommGroup B]` placed after the group variables and before
  `A`, then the common data telescope, then explicit
  `f : ambientFixedAddSubgroup A K →+ B` and
  `hf : finiteNormSubgroup A K L hLK ≤ f.ker`. Its result is
  `FiniteNormQuotient A K L hLK →+ B` with source body
  `unfold FiniteNormQuotient; exact QuotientAddGroup.lift (finiteNormSubgroup A K L hLK) f hf`.
  It has a second, independent universe parameter for `B`.

## Reused objects

`relativeNorm` and its finite-instance binder come from the published
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions`,
which also supplies `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup`
(M023.001). Source `CyclicCohomology.extensionSubgroup K L hLK` (M004.002,
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 47–54,
SHA-256 `06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`)
is an abbreviation with body `L.toSubgroup.subgroupOf K.toSubgroup`; each
occurrence is replaced by that exact Mathlib term, as in the published M024
and M010 modules, so the instance binders agree syntactically with those of
`relativeNorm`. The inclusion parameter `hLK` remains in every telescope.

## Modifications

Worker 96 made only the following adaptations on 14 November 2026:

1. Prefix `ClassFormation` by `Langlands.NYLL`; replace the original imports
   by the focused published relative norm module. Drop the unused
   `open CyclicCohomology` and the `universe u` declaration, which only the
   unported `finiteIntermediateField` section uses.
2. Expand `extensionSubgroup` as described above, with parentheses.
3. Extract only the seven listed declarations; keep the `section finiteNorms`
   structure and replace the module introduction with an extraction notice.

All declaration bodies, binder kinds and instance orders are unchanged.

## Development verification and scope

The module compiles with zero errors and warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean v4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

A private probe reconstructs all seven source declarations verbatim, with the
original `extensionSubgroup` abbreviation in each instance binder, and checks
each against its adapted counterpart as an entire dependent function, before
application: `rfl` equalities for `finiteNormSubgroup`, `FiniteNormQuotient`
and `finiteNormClass`, and `HEq.rfl` for the instance, the equivalence, the
class homomorphism and the lift, whose types mention the reconstructed
quotient. The lift is compared at two arbitrary independent universes. The
probe supplies no public declaration.

This support data is internal to the NYLL abstract-field model. The theorems
about it are separate statement targets; the host class-formation, cup,
transfer, Tate and reciprocity obligations remain with their existing owners.

## Attribution

The original copyright, author and Apache-2.0 header is retained verbatim.
The existing Library files `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained, with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 96's modifications are recorded in the Lean header and above.
