# NYLL M028.002: fixed-field inclusion coercion target

The paired Lean file adapts the statement of
`ClassFormation.fixedFieldInclusion_coe` from Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean`,
M028.002. The source docstring is at lines 38–41, the `simp` attribute at
line 42, the complete theorem telescope and equality at lines 43–46, and
the source proof `rfl` at line 47. The enclosing namespace, open,
noncomputable section and group variables are at lines 16–27.
The source file SHA-256 is
`9b2f91f76898d32b4f6f556a6b628aa0c4cf40768f43423b15e81de22fadc4bf`.

The registered original source is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL-specific erratum was found among the available project errata notes.

## Statement and complete telescope

The name correspondence is:

| Original | Adapted |
| --- | --- |
| `ClassFormation.fixedFieldInclusion_coe` | `Langlands.NYLL.ClassFormation.fixedFieldInclusion_coeStatement` |
| `ClassFormation.fixedFieldInclusion` | `Langlands.NYLL.ClassFormation.fixedFieldInclusion` |
| `KummerTheory.ambientFixedAddSubgroup` | `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` |
| `IntegralRepGroupType` | `Langlands.NYLL.IntegralRepGroupType` |

The target has the source's full telescope and equality:

```lean
def Langlands.NYLL.ClassFormation.fixedFieldInclusion_coeStatement
    {G : Langlands.NYLL.IntegralRepGroupType}
    [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup A K) : Prop :=
  ((Langlands.NYLL.ClassFormation.fixedFieldInclusion A K L hLK a :
      Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup A L) : A.V) = a.1
```

It states that including a `K`-fixed element into the `L`-fixed subgroup and
then coercing back to `A.V` returns its original ambient value. The inclusion
hypothesis has direction `L.toSubgroup ≤ K.toSubgroup`.

The group remains in `Type 0` through the published alias, while the carrier
universe of `Rep ℤ G` remains free. Binder order and kinds are unchanged:
implicit `G`, group and topology instances, then explicit `A`, `K`, `L`,
`hLK` and `a`. The source's `{D : DegreeData G}` and earlier implicit `{A}`
at line 28 are unused section variables, absent from the source theorem's
elaborated telescope. There is no degree-data, valuation, normality or
finiteness hypothesis.

## Modification record

Worker 290 made these changes:

1. Prefix the namespace with `Langlands.NYLL` and resolve source references
   to the adapted names in the table.
2. Replace `theorem fixedFieldInclusion_coe ... : equality := rfl` by
   `def fixedFieldInclusion_coeStatement ... : Prop := equality`. The equality
   itself is copied verbatim. The source proof and `@[simp]` attribute are
   omitted: this contribution publishes a proposition target; a proof is
   separate work.
3. Replace the source `ValuationLaws` import by the focused
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions`
   import, which supplies exactly the inclusion construction used here.
4. Omit unused `open CyclicCohomology` and the unused section variables from
   line 28. Retain `open KummerTheory`, the noncomputable section and the
   group-variable comment. Replace the source declaration/module docstrings
   by descriptions of the proposition target and add a modification notice.
5. Omit all other source units. No helper declaration or global instance is
   added.

This is the exact source equality as a named `Prop`, without a published
proof. It discharges no host class-formation, cup, transfer, Tate or reciprocity
target.

## Verification

The focused statement module, proposition return type and full unapplied
declaration telescope passed a project Lean service check on 13 November 2026
with environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Declaration inspection reported
`statement_returns_prop: true`, a single free carrier universe parameter,
and only `propext` and `Quot.sound` among its axioms. A private probe assigned
the unapplied constant to the full expected telescope at arbitrary carrier
universe `u`, and checked by reflexivity that the target body is exactly the
source equality. The paired statement has no diagnostics; the probe's warnings
concern only binders deliberately retained for full-type checks. Compilation
and declaration inspection are separate from independent semantic acceptance
and publication.

## Attribution

The original copyright, Apache-2.0 release and author header are retained
verbatim. The published `licenses/NYLL/LICENSE` has SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`;
`licenses/NYLL/NOTICE` has SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
