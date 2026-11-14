# NYLL M028: relative norms of included and trivial-extension elements

The paired Lean file adapts two theorem statements from Naganori Yamaguchi's
ClassFieldTheory at pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean`,
SHA-256
`9b2f91f76898d32b4f6f556a6b628aa0c4cf40768f43423b15e81de22fadc4bf`.
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
| M028.003 | `relativeNorm_fixedFieldInclusion` | 49–55 (docstring 49) | 56–75 | `relativeNorm_fixedFieldInclusionStatement` |
| M028.004 | `relativeNorm_self` | 77–83 (docstring 77, `@[simp]` 78) | 84–105 | `relativeNorm_selfStatement` |

The enclosing source context is `namespace ClassFormation` (line 16),
`open KummerTheory` (line 18), `open CyclicCohomology` (line 20),
`noncomputable section` (line 24), the group variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 27) and the
section variables `{D : DegreeData G} {A : Rep ℤ G}` (line 28). Neither
section variable occurs in these two declarations: each has its own explicit
`A`, which shadows the section variable, and `D` is unused, so Lean does not
include them. The adapted file therefore declares only the line 27 variables
and the resulting telescopes are identical.

Each theorem becomes a `def` returning `Prop`; its body is the original
assertion after the namespace change and abbreviation expansion below. The
original proofs are separate obligations.

## Complete parameters and assertions

Both targets begin with implicit `{G : IntegralRepGroupType}`, `[Group G]` and
`[TopologicalSpace G]`; `Langlands.NYLL.IntegralRepGroupType` is `Type 0`.
The representation carrier has an arbitrary universe, giving each declaration
one universe parameter.

`relativeNorm_fixedFieldInclusionStatement` then takes, explicitly and in
order, `A : Rep ℤ G`, `E : DegreeData.FiniteAbstractExtension G` and
`a : ambientFixedAddSubgroup A E.base`. Its assertion is

```lean
relativeNorm A E.base E.field E.below
    (fixedFieldInclusion A E.base E.field E.below a) =
  (E.degree : ℕ) • a
```

in the additive group `ambientFixedAddSubgroup A E.base` (the fixed module
`A_K` of the base). Here `fixedFieldInclusion` (M028.001) is the inclusion
`A_K →+ A_L`, `relativeNorm` (M024.009) is the coset-sum norm `A_L →+ A_K`,
and `E.degree : ℕ+` is the positive degree of the finite abstract extension,
coerced to `ℕ`. The finiteness instance needed by `relativeNorm` is not a
hypothesis: as in the source, it is found by instance search, now from the
published `DegreeData.FiniteAbstractExtension.representedQuotientFinite`
(source `Degree/Fields.lean`, lines 646–652), whose type is
`Finite (E.base.toSubgroup ⧸ (E.field.toSubgroup.subgroupOf E.base.toSubgroup))`.

`relativeNorm_selfStatement` takes explicit `A : Rep ℤ G` and
`K : ClosedSubgroup G`, then the instance
`[Finite (K.toSubgroup ⧸ (K.toSubgroup.subgroupOf K.toSubgroup))]`, then
explicit `a : ambientFixedAddSubgroup A K`. Its assertion is

```lean
relativeNorm A K K le_rfl a = a
```

that is, the norm of the trivial extension `K | K` (with inclusion proof
`le_rfl`) is the identity on `A_K`. The finiteness instance is retained as a
hypothesis exactly as in the source, although it always holds.

## Reused objects and modifications

The imports supply published data by Lean name:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions`:
  `relativeNorm` (M024.009), and through it
  `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` (M023.001);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions`:
  `fixedFieldInclusion` (M028.001);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions`:
  `DegreeData.FiniteAbstractExtension` (M010.065), its `degree` (M010.085)
  and the instance `representedQuotientFinite`.

Source `CyclicCohomology.extensionSubgroup K K le_rfl` (M004.002,
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 47–54, SHA-256
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`) is an
abbreviation whose body is `L.toSubgroup.subgroupOf K.toSubgroup`; in
`relativeNorm_selfStatement` it is expanded to the exact Mathlib term
`K.toSubgroup.subgroupOf K.toSubgroup`, matching the published M024 data and
`relativeNorm`'s instance binder.

Worker 96 made only the following adaptations on 14 November 2026:

1. Prefix the namespace by `Langlands.NYLL` and replace the original import
   by the three focused published modules above. Drop the unused
   `open CyclicCohomology` and the unused section variables.
2. Expand `extensionSubgroup` by its exact body, with parentheses.
3. Convert each theorem into the listed Prop-valued `def` with the
   `Statement` suffix, keeping the source hypotheses, binder kinds and order
   and the entire assertion. Omit the proofs and the `@[simp]` attribute of
   M028.004, which belongs to a proved equation.
4. Keep `noncomputable section`, replace the module introduction with an
   extraction notice, and mark the docstrings as targets.

No instance or helper declaration is introduced.

## Development verification and scope

The module compiles with zero errors and warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean v4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Focused inspection of each target
succeeds and reports `statement_returns_prop = true`.

A private probe reconstructs both source assertions in the source context
(including the line 28 section variables and, for M028.004, the original
`extensionSubgroup K K le_rfl` instance) and verifies equality of the entire
dependent functions with the adapted ones by `rfl` for an arbitrary carrier
universe. The probe supplies no public declaration.

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
