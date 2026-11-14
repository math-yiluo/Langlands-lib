# NYLL M026: relative-norm invariance and tower transitivity

The paired Lean file adapts two theorem statements from Naganori Yamaguchi's
ClassFieldTheory at pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`,
SHA-256
`985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f`.
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

Every original name below has prefix `ClassFormation.` and every adapted
name has prefix `Langlands.NYLL.ClassFormation.`.

| Unit | Source name | Statement lines | Original proof lines | Adapted Prop definition |
| --- | --- | --- | --- | --- |
| M026.013 | `relativeNorm_normalExtensionAction` | 284–293 (docstring 284–285) | 294–313 | `relativeNorm_normalExtensionActionStatement` |
| M026.019 | `DegreeData.FiniteTower.norm_trans_apply` | 437–444 (docstring 437–438) | 445–446 | `DegreeData.FiniteTower.norm_trans_applyStatement` |

The enclosing source context is `namespace ClassFormation` (line 16),
`open KummerTheory` (line 18), `open CyclicCohomology` (line 20),
`noncomputable section` (line 24), `open scoped BigOperators Pointwise`
(line 26) and the group variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 29). For
M026.019 it also includes `namespace DegreeData.FiniteTower` (line 433) and
the section variable `(T : DegreeData.FiniteTower G)` (line 435), which the
statement uses and Lean therefore includes. The adapted file reproduces this
context; the opens of `CyclicCohomology`, `BigOperators` and `Pointwise` are
dropped because, after the abbreviation expansion below, neither assertion
uses them.

Each theorem becomes a `def` returning `Prop`; its body is the original
assertion after the namespace change and abbreviation expansion. The original
proofs are separate obligations.

## Complete parameters and assertions

Both targets begin with implicit `{G : IntegralRepGroupType}`, `[Group G]` and
`[TopologicalSpace G]`; `Langlands.NYLL.IntegralRepGroupType` is `Type 0`.
The representation carrier has an arbitrary universe, giving each declaration
one universe parameter.

`relativeNorm_normalExtensionActionStatement` then takes, in source order,
explicit `A : Rep ℤ G`, `K L : ClosedSubgroup G`,
`hLK : L.toSubgroup ≤ K.toSubgroup` and
`hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal`, then the instance
`[Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]`, then
explicit `k : K.toSubgroup` and `a : ambientFixedAddSubgroup A L`. Its
assertion is

```lean
relativeNorm A K L hLK (normalExtensionAction A K L hLK hnormal k a) =
  relativeNorm A K L hLK a
```

in `ambientFixedAddSubgroup A K`: for a finite Galois abstract extension
`L | K` (normality of `G_L` in `G_K`), the coset-sum norm `A_L → A_K` is
invariant under the action of `k ∈ G_K` on `A_L` given by
`normalExtensionAction` (M026.011), whose underlying vector is `A.ρ k a`.

`DegreeData.FiniteTower.norm_trans_applyStatement` takes explicit
`T : DegreeData.FiniteTower G`, `A : Rep ℤ G` and
`a : ambientFixedAddSubgroup A T.top`. Its assertion is

```lean
relativeNorm A T.base T.middle T.middle_le_base
    (relativeNorm A T.middle T.top T.top_le_middle a) =
  relativeNorm A T.base T.top
    (T.top_le_middle.trans T.middle_le_base) a
```

that is, `N_{middle|base} ∘ N_{top|middle} = N_{top|base}` on the fixed module
of the top field. As in the source, the three finiteness instances required by
`relativeNorm` are not hypotheses; they come from the tower `T` by instance
search. The published instances with these types are
`DegreeData.FiniteTower.topQuotientFinite` and
`DegreeData.FiniteTower.baseQuotientFinite` (M010, source `Degree/Fields.lean`
lines 925–929 and 931–935) and `DegreeData.FiniteTower.totalQuotientFinite` (M026.016, source lines
340–345). Since `Finite` is a proposition, the assertion does not depend on
which instance term is chosen.

## Reused objects and modifications

The imports supply published data by Lean name:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions`:
  `relativeNorm` (M024.009), and through it
  `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` (M023.001);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions`:
  `normalExtensionAction` (M026.011) and the instance
  `DegreeData.FiniteTower.totalQuotientFinite` (M026.016);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteTower.Definitions`:
  `DegreeData.FiniteTower` with its instances `topQuotientFinite` and
  `baseQuotientFinite`.

Source `CyclicCohomology.extensionSubgroup K L hLK` (M004.002,
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 47–54, SHA-256
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`) is an
abbreviation whose body is `L.toSubgroup.subgroupOf K.toSubgroup`. In the
`hnormal` binder and the finiteness instance binder of M026.013 it is
expanded to that exact Mathlib term, matching the binder of the published
`relativeNorm`. Because the published `extensionSubgroup` is a reducible
`abbrev` with the same body, `hnormal` is passed unchanged to the published
`normalExtensionAction`, whose binder is stated with `extensionSubgroup`.

Worker 96 made only the following adaptations on 14 November 2026:

1. Prefix the namespace by `Langlands.NYLL` and replace the original imports
   by the three focused published modules above. Drop the opens that are not
   used.
2. Expand `extensionSubgroup` by its exact body, with parentheses.
3. Convert each theorem into the listed Prop-valued `def` with the
   `Statement` suffix, keeping the source hypotheses, binder kinds and order
   and the entire assertion. Omit the proofs.
4. Keep `noncomputable section`, replace the module introduction with an
   extraction notice, and mark the docstrings as targets.

No instance or helper declaration is introduced.

## Development verification and scope

The module compiles with zero errors and warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean v4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Focused inspection of each target
succeeds and reports `statement_returns_prop = true`.

A private probe restates both source assertions in the source form (for
M026.013 with the original `extensionSubgroup K L hLK` in both binders) and
verifies equality of the entire dependent functions with the adapted ones by
`rfl` for an arbitrary carrier universe. The probe supplies no public
declaration.

These are statement targets in the NYLL abstract-field model; their proofs
belong to separate `lean.proof@1` tasks after publication. The host
class-formation, cup, transfer, Tate and reciprocity obligations remain with
their existing owners.

## Attribution

The original copyright, author and Apache-2.0 header is retained verbatim.
The existing Library files `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained, with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The Lean modification notice and this Markdown identify every adaptation.
