# Relative norms on actual fixed fields: statement

This module defines one closed proposition,
`Langlands.NYLL.LocalClassFieldTheory.relativeNorm_abstractFixedFieldUnit_eq_normUnitsStatement : Prop`,
the statement phase of source row M276.008, the theorem
`LocalClassFieldTheory.relativeNorm_abstractFixedFieldUnit_eq_normUnits`.
The module contains no proof. A separate proof child will prove it under the
name `Langlands.NYLL.LocalClassFieldTheory.relativeNorm_abstractFixedFieldUnit_eq_normUnits`.

## Complete closed telescope

The source declares the section variables
`(k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] [IsSepClosed Ω]`.
A theorem includes every instance section variable whose types mention only
included variables, unless it is omitted. The source theorem has no `omit`,
so it has both `[IsGalois k Ω]` and `[IsSepClosed Ω]`. The statement
quantifies these binders and then the theorem's own binders, in the source
order. Its body is

```lean
∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsSepClosed Ω]
  (K L : ClosedSubgroup (Gal(Ω/k)))
  (hLK : L.toSubgroup ≤ K.toSubgroup)
  [Finite
    (K.toSubgroup ⧸
      Langlands.NYLL.CyclicCohomology.extensionSubgroup K L hLK)]
  [Finite
    ((Langlands.NYLL.ClassFormation.baseField Gal(Ω/k)).toSubgroup ⧸
      Langlands.NYLL.CyclicCohomology.extensionSubgroup
        (Langlands.NYLL.ClassFormation.baseField Gal(Ω/k)) K
        (Langlands.NYLL.ClassFormation.le_baseField K))]
  (x : (abstractRelativeFixedField k Ω hLK)ˣ),
  Langlands.NYLL.ClassFormation.relativeNorm
      (galoisAmbientUnitsRep k Ω) K L hLK
      (abstractRelativeFixedFieldUnitsEquivGaloisFixed
        k Ω K L hLK (Additive.ofMul x)) =
    abstractFixedFieldUnitsEquivGaloisFixed k Ω K
      (Additive.ofMul
        (Langlands.NYLL.LocalFieldTheory.normUnits
          (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK) x))
```

(the unqualified names are in `Langlands.NYLL.LocalClassFieldTheory`, the
namespace of the definition). The source names the two finiteness instance
binders `hfinite` and `hKabsolute`. They are used only in the omitted
proof, so here they are anonymous instance binders in the same places. The
second binder is not used by the asserted equation; it stays as a premise
because the source theorem has it.

## Meaning

Let `Ω / k` be Galois with `Ω` separably closed, and let `L ≤ K` be closed
subgroups of `Gal(Ω/k)`. Write `Ω^K` for `abstractFixedField k Ω K` and
`Ω^L` for `abstractRelativeFixedField k Ω hLK`, the fixed field of `L`
viewed as an `Ω^K`-algebra. The two premises say that `L` has finite index
in `K` and that `K` has finite index in the whole group
`baseField Gal(Ω/k)`, whose underlying subgroup is all of `Gal(Ω/k)`.

- `galoisAmbientUnitsRep k Ω` is the representation of `Gal(Ω/k)` on `Ωˣ`,
  written additively.
- `abstractRelativeFixedFieldUnitsEquivGaloisFixed k Ω K L hLK` and
  `abstractFixedFieldUnitsEquivGaloisFixed k Ω K` identify
  `Additive (Ω^L)ˣ` and `Additive (Ω^K)ˣ` with the `L`- and `K`-fixed
  vectors of that representation.
- `relativeNorm A K L hLK` is the class-formation norm from `L`-fixed to
  `K`-fixed vectors of `A`: the sum, over a system of representatives of
  the left cosets of `L` in `K`, of their actions. Written
  multiplicatively for `A = Ωˣ`, it is the product of the conjugates.
- `normUnits (Ω^K) (Ω^L)` is `Units.map (Algebra.norm (Ω^K))`, the field
  norm on units.

So the statement says: for a unit `x` of `Ω^L`, the product of the coset
conjugates of `x` in `Ωˣ`, a `K`-fixed unit, is the unit of `Ω^K` given by
the field norm `N_{Ω^L/Ω^K}(x)`. No normality of `Ω^L` over `Ω^K` is
assumed.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M024.009, `ClassFormation.relativeNorm` | `Langlands.NYLL.ClassFormation.relativeNorm`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions` |
| M010.003, `ClassFormation.baseField` | `Langlands.NYLL.ClassFormation.baseField`, reached through the next module |
| M010.005, `ClassFormation.le_baseField` | `Langlands.NYLL.ClassFormation.le_baseField : le_baseFieldStatement K`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs` |
| M004.002, `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup`, module `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions` |
| M088.001, `LocalClassFieldTheory.galoisAmbientUnitsRep` | `Langlands.NYLL.LocalClassFieldTheory.galoisAmbientUnitsRep`, reached through the next module |
| M101.001, `LocalClassFieldTheory.abstractFixedFieldUnitsEquivGaloisFixed` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldUnitsEquivGaloisFixed`, reached through the next module |
| M101.003, `LocalClassFieldTheory.abstractRelativeFixedFieldUnitsEquivGaloisFixed` | `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedFieldUnitsEquivGaloisFixed`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Relative.Definitions` |
| M099.001 / M099.009, `abstractFixedField` / `abstractRelativeFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField`, `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedField`, reached through the previous module |
| M092.002, `LocalFieldTheory.normUnits` | `Langlands.NYLL.LocalFieldTheory.normUnits`, module `Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions` |
| Mathlib `ClosedSubgroup`, `IsGalois`, `IsSepClosed`, `Finite`, `Additive` | Used unchanged; `IsSepClosed` is imported from `Mathlib.FieldTheory.IsSepClosed` |

The published `le_baseField K` proves `le_baseFieldStatement K`, which
unfolds to `K.toSubgroup ≤ (baseField G).toSubgroup`, so it is accepted as
the inequality argument of `extensionSubgroup`, as in the source. The
published `relativeNorm` asks for
`[Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]`; the
reducible abbreviation `extensionSubgroup K L hLK` has this body, so
instance search finds the first premise.

The compiled declaration was checked with `#print` (Lean v4.34.0): it is a
`def` of type `Prop` whose body is the proposition above.

## Library search

The whole Library at commit `4f4af6baed8c8e029e87c8303ea44c8f1d9f2f86`
was searched for `relativeNorm_abstractFixedFieldUnit`,
`abstractFixedFieldUnit_eq_normUnits`, for files using both
`relativeNorm` and `normUnits` or `Algebra.norm`, and for uses of
`abstractFixedFieldUnitsEquivGaloisFixed`. The name occurs only in the
planning note `notes/reuse/nyll-public-port/m270-m288.md`. The fixed-unit
equivalences also occur in the published M276.007 target in
`FixedFieldRelativeNorm/U004/Statements.lean`; that target compares individual
coset actions rather than the entire relative norm.
The files outside `Langlands/NYLL` that mention both relative norms and
unit norms, such as `Langlands/ClassFieldTheory/Local/UnitNormProof.lean`,
concern integer rings of local field extensions and do not use the NYLL
class-formation norm. So nothing in the Library already covers M276.008.

## Original source

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldRelativeNorm.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldRelativeNorm.lean>).
The file was read; its SHA-256 is
`ab3ee25eed6dbccd721f18245bc5f17aea6fbe8e7631a11f41e9eb88032c1e4c`.
The header is at lines 1–5, the imports at 7–10, the module docstring at
12–20, `noncomputable section` at 24, the namespace at 28, the `open` lines
at 30–31 and the `variable` line at 33–34.

| Source unit and original declaration | Source lines | Adapted declaration |
| --- | --- | --- |
| M276.008, `LocalClassFieldTheory.relativeNorm_abstractFixedFieldUnit_eq_normUnits` | docstring 189–191, signature 192–208, proof 209–273 (omitted) | `Langlands.NYLL.LocalClassFieldTheory.relativeNorm_abstractFixedFieldUnit_eq_normUnitsStatement` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 56 extracted the asserted type directly from the pinned original on
14 November 2026 and made these changes:

- The theorem becomes a Prop-valued definition with the `Statement`
  suffix. Its complete telescope, including the section variables it uses,
  moves inside the proposition in the same order and with the same binder
  kinds and the source's universe-zero `Type`. The named instance binders
  `hfinite` and `hKabsolute` become anonymous instance binders. The proof
  is omitted for the separate proof phase.
- The name keeps the source name with the `Langlands.NYLL` prefix and the
  `Statement` suffix; the source docstring is kept.
- Published names are written in full where the source relies on its
  `open` lines.
- The source imports are replaced by `Mathlib.FieldTheory.IsSepClosed` and
  the five published modules listed above.
- The local instance M276.001, the definitions M276.002 and M276.006, the
  theorems M276.003–M276.005 and M276.007 and all other declarations of the
  source file are omitted.

No instance or simp attribute is installed. No shared draft or other
worker's unpublished work was reused.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance, and the Apache-2.0
notice, followed by a dated modification record. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Scope

This unit contains only this statement. Its truth proof belongs to a
separate proof unit published after the statement is accepted. The source
proof uses `abstractRelativeFixedField_finiteDimensional` (M099.019), the
definition `abstractFixedFieldCosetEquivAlgHom` (M276.006) and the theorem
`relativeCosetAction_abstractFixedFieldUnit_val` (M276.007).
