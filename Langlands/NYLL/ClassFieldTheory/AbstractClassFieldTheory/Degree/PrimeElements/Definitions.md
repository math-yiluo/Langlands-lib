# NYLL M028.001: inclusion of ambient fixed additive subgroups

The paired Lean file adapts `ClassFormation.fixedFieldInclusion` from
Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean`,
M028.001. The source definition and its docstring occupy lines 30–36; the
relevant namespace, open, noncomputable section and group variables are at
lines 16–27. The source file SHA-256 is
`9b2f91f76898d32b4f6f556a6b628aa0c4cf40768f43423b15e81de22fadc4bf`.

The registered original source is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL-specific erratum was found among the available project errata notes.

## Construction and complete telescope

The name correspondence is:

| Original | Adapted |
| --- | --- |
| `ClassFormation.fixedFieldInclusion` | `Langlands.NYLL.ClassFormation.fixedFieldInclusion` |
| `KummerTheory.ambientFixedAddSubgroup` | `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` |
| `IntegralRepGroupType` | `Langlands.NYLL.IntegralRepGroupType` |

The definition has the source telescope:

```lean
def Langlands.NYLL.ClassFormation.fixedFieldInclusion
    {G : Langlands.NYLL.IntegralRepGroupType}
    [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup A K →+
      Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup A L
```

`G` remains in `Type 0`, through the published `IntegralRepGroupType` alias.
The carrier universe of `Rep ℤ G` remains free, as in the source's unannotated
`Rep ℤ G`. The order and kinds of every binder are preserved: implicit group,
the group and topology instances, then explicit `A`, `K`, `L`, and `hLK`.
No `DegreeData` parameter occurs. The source's earlier section variables
`{D : DegreeData G}` and `{A : Rep ℤ G}` at line 28 are unused in this
declaration, whose explicit `A` shadows that section variable.

An element of `ambientFixedAddSubgroup A K` is an element of `A.V` fixed by
every member of `K`. Since `hLK` includes `L` in `K`, this element is also fixed
by every member of `L`. The additive homomorphism keeps the ambient value and
restricts the witness of fixedness:

```lean
toFun a := ⟨a.1, fun l => a.2 ⟨l.1, hLK l.2⟩⟩
map_zero' := rfl
map_add' _ _ := rfl
```

These three fields, including their proof terms, are copied verbatim. The map
goes from the `K`-fixed subgroup to the `L`-fixed subgroup. It is defined for
any closed subgroup inclusion and integral representation; no finiteness,
normality, continuity of the representation, valuation or class-formation
hypothesis is added.

## Modification record

Worker 290 made only these changes:

1. Prefix the source namespace `ClassFormation` with `Langlands.NYLL`, using
   the published names in the table above.
2. Replace the source import
   `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws` by
   `Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions`.
   This supplies the actual fixed additive subgroup and, transitively, Mathlib's
   `Rep` and `ClosedSubgroup` plus the published universe alias. No declaration
   from `ValuationLaws` is used by this unit.
3. Omit the unused `open CyclicCohomology` and the unused source section
   variables at line 28. Keep `open KummerTheory`, the noncomputable section,
   the source group-variable comment, declaration docstring and definition.
4. Replace the module description and add the explicit modification record.
   Other source declarations are outside this definition unit.

The lexical dependency on
`ClassFormation.DegreeData.FiniteResidueAbstractField.toSubgroup` is spurious:
both `K.toSubgroup` and `L.toSubgroup` are projections of Mathlib's
`ClosedSubgroup`. No substitute definition, helper declaration or instance is
introduced. This unit discharges no host class-formation, cup, transfer, Tate
or reciprocity target.

## Verification

The focused module and complete unapplied declaration telescope passed a
project Lean service check on 13 November 2026 with environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. A private probe assigned the
unapplied constant to the full expected telescope for `Rep.{u} ℤ G`; this
passed. Printed declaration inspection shows a single free universe parameter
for the representation carrier and no degree-data parameter. The paired
definition has no diagnostics; the private probe's warnings concern only
binders deliberately retained for the full-type checks. Development checks
are separate from independent semantic acceptance and publication.

## Attribution

The original copyright, Apache-2.0 release and author header are retained
verbatim. The published `licenses/NYLL/LICENSE` has SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`;
`licenses/NYLL/NOTICE` has SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
