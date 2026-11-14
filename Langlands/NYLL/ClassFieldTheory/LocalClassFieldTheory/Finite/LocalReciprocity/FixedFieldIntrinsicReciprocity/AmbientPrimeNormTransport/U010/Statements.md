# Relative norms of abstract relative fixed-field units: statement

This module defines one closed proposition,
`Langlands.NYLL.LocalClassFieldTheory.relativeNorm_preimage_abstractRelativeFixedFieldUnitStatement : Prop`,
the statement phase of source row M283.010, the theorem
`LocalClassFieldTheory.relativeNorm_preimage_abstractRelativeFixedFieldUnit`.
The module contains no proof. A separate proof child will prove it under the
name
`Langlands.NYLL.LocalClassFieldTheory.relativeNorm_preimage_abstractRelativeFixedFieldUnit`.

## Complete closed telescope

The source theorem has no section variables; its binders are its own. The
statement quantifies them in the source order, with the same binder kinds
and the source's universe-zero `Type`. Its body is

```lean
∀ (K : Type) [Field K]
  (H L : ClosedSubgroup Gal(SeparableClosure K/K))
  (hLH : L.toSubgroup ≤ H.toSubgroup)
  [Finite
    (H.toSubgroup ⧸
      Langlands.NYLL.CyclicCohomology.extensionSubgroup H L hLH)]
  [Finite
    ((Langlands.NYLL.ClassFormation.baseField
      Gal(SeparableClosure K/K)).toSubgroup ⧸
      Langlands.NYLL.CyclicCohomology.extensionSubgroup
        (Langlands.NYLL.ClassFormation.baseField Gal(SeparableClosure K/K))
        H (Langlands.NYLL.ClassFormation.le_baseField H))]
  (p : (abstractRelativeFixedField
    K (SeparableClosure K) hLH)ˣ)
  (x : (abstractFixedField K (SeparableClosure K) H)ˣ),
  Langlands.NYLL.LocalFieldTheory.normUnits
      (abstractFixedField K (SeparableClosure K) H)
      (abstractRelativeFixedField K (SeparableClosure K) hLH)
      p =
    x →
    Additive.toMul
        ((abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) H).symm
          (Langlands.NYLL.ClassFormation.relativeNorm
            (galoisAmbientUnitsRep K (SeparableClosure K))
            H L hLH
            (abstractRelativeFixedFieldUnitsEquivGaloisFixed
              K (SeparableClosure K) H L hLH
                (Additive.ofMul p)))) =
      x
```

(the unqualified names are in `Langlands.NYLL.LocalClassFieldTheory`, the
namespace of the definition). The source hypothesis `hnorm`, which the
conclusion does not mention, is the unnamed implication premise
`normUnits … p = x →` in its source position. The two finiteness instance
binders are anonymous in the source and stay anonymous. The objects
`abstractFixedField K (SeparableClosure K) H` and its relatives need
`[IsGalois K (SeparableClosure K)]`; as in the source, instance search finds
Mathlib's Galois instance for the separable closure, so no Galois binder
appears.

The compiled declaration was checked with `#print` (Lean v4.34.0): it is a
`def` of type `Prop` whose body is the proposition above.

## Meaning

Let `K` be a field with separable closure `K^sep`, and let `L ≤ H` be closed
subgroups of `Gal(K^sep/K)`. Write `K^sep_H` for
`abstractFixedField K (SeparableClosure K) H` and `K^sep_L` for
`abstractRelativeFixedField K (SeparableClosure K) hLH`, the fixed field of
`L` viewed as a `K^sep_H`-algebra. The two premises say that `L` has finite
index in `H` and that `H` has finite index in the whole group
`baseField Gal(K^sep/K)`, whose underlying subgroup is all of
`Gal(K^sep/K)`.

- `galoisAmbientUnitsRep K (SeparableClosure K)` is the representation of
  `Gal(K^sep/K)` on `(K^sep)ˣ`, written additively.
- `abstractRelativeFixedFieldUnitsEquivGaloisFixed K (SeparableClosure K) H L hLH`
  and `abstractFixedFieldUnitsEquivGaloisFixed K (SeparableClosure K) H`
  identify `Additive (K^sep_L)ˣ` and `Additive (K^sep_H)ˣ` with the `L`- and
  `H`-fixed vectors of that representation; `.symm` is the inverse
  identification.
- `relativeNorm A H L hLH` is the class-formation norm from `L`-fixed to
  `H`-fixed vectors of `A`: the sum, over a system of representatives of the
  left cosets of `L` in `H`, of their actions, that is the product of the
  conjugates for `A = (K^sep)ˣ`.
- `normUnits (K^sep_H) (K^sep_L)` is `Units.map (Algebra.norm (K^sep_H))`,
  the field norm on units.

So the statement says: if `x` is the field norm of the unit `p` of
`K^sep_L` down to `K^sep_H`, then the class-formation relative norm of `p`,
read back as a unit of `K^sep_H`, is `x`. It is the specialization of the
theorem `relativeNorm_abstractFixedFieldUnit_eq_normUnits` (source row
M276.008) to `Ω = K^sep`, read through the inverse of the fixed-unit
identification.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M024.009, `ClassFormation.relativeNorm` | `Langlands.NYLL.ClassFormation.relativeNorm`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions` |
| M010.003, `ClassFormation.baseField` | `Langlands.NYLL.ClassFormation.baseField`, reached through the next module |
| M010.005, `ClassFormation.le_baseField` | `Langlands.NYLL.ClassFormation.le_baseField : le_baseFieldStatement H`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs` |
| M004.002, `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup`, module `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions` |
| M088.001, `LocalClassFieldTheory.galoisAmbientUnitsRep` | `Langlands.NYLL.LocalClassFieldTheory.galoisAmbientUnitsRep`, reached through the next module |
| M101.001, `LocalClassFieldTheory.abstractFixedFieldUnitsEquivGaloisFixed` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldUnitsEquivGaloisFixed`, reached through the next module |
| M101.003, `LocalClassFieldTheory.abstractRelativeFixedFieldUnitsEquivGaloisFixed` | `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedFieldUnitsEquivGaloisFixed`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Relative.Definitions` |
| M099.001 / M099.009, `abstractFixedField` / `abstractRelativeFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField`, `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedField`, reached through the previous module |
| M092.002, `LocalFieldTheory.normUnits` | `Langlands.NYLL.LocalFieldTheory.normUnits`, module `Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions` |
| Mathlib `SeparableClosure` and its `IsGalois` instance, `ClosedSubgroup`, `Finite`, `Additive`, `AddEquiv.symm` | Used unchanged; `SeparableClosure` is imported from `Mathlib.FieldTheory.IsSepClosed` |

The published `le_baseField H` proves `le_baseFieldStatement H`, which
unfolds to `H.toSubgroup ≤ (baseField G).toSubgroup`, so it is accepted as
the inequality argument of `extensionSubgroup`, as in the source. The
published `relativeNorm` asks for
`[Finite (H.toSubgroup ⧸ L.toSubgroup.subgroupOf H.toSubgroup)]`; the
reducible abbreviation `extensionSubgroup H L hLH` has this body, so
instance search finds the first premise.

## Library search

The whole Library at commit `4f4af6baed8c8e029e87c8303ea44c8f1d9f2f86`
was searched for `relativeNorm_preimage`,
`preimage_abstractRelativeFixedFieldUnit`, for files using both
`relativeNorm` and `normUnits` or `Algebra.norm`, and for uses of
`abstractFixedFieldUnitsEquivGaloisFixed`. The name occurs only in the
planning note `notes/reuse/nyll-public-port/m270-m288.md`. The fixed-unit
equivalences are used only in their own `AbstractFixedFieldUnits` modules.
The files outside `Langlands/NYLL` that mention both relative norms and
unit norms, such as `Langlands/ClassFieldTheory/Local/UnitNormProof.lean`,
concern integer rings of local field extensions and do not use the NYLL
class-formation norm. The general form M276.008 is a separate unit of this
port, staged as the statement candidate
`f5b4086a-91ef-46bf-b038-a28bbb3f4a75` and not yet in the Library. So
nothing in the Library already covers M283.010.

## Original source

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean>).
The file was read; its SHA-256 is
`b430f3810416cb42cc7c61df63be3691b219a5fe39c0bc7c0c2a74292298bfa0`.
The header is at lines 1–5, the imports at 7–8, the module docstring at
10–16, `noncomputable section` at 20, the namespace at 22 and the `open`
lines at 24–26.

| Source unit and original declaration | Source lines | Adapted declaration |
| --- | --- | --- |
| M283.010, `LocalClassFieldTheory.relativeNorm_preimage_abstractRelativeFixedFieldUnit` | docstring 344–345, signature 346–377, proof 378–403 (omitted) | `Langlands.NYLL.LocalClassFieldTheory.relativeNorm_preimage_abstractRelativeFixedFieldUnitStatement` |

The source proof (omitted here) rewrites the relative norm with the source
theorem `relativeNorm_abstractFixedFieldUnit_eq_normUnits` (source row
M276.008) and with `hnorm`, and then cancels the fixed-unit equivalence
against its inverse. The proof phase therefore needs the published proof of
M276.008.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 56 extracted the asserted type directly from the pinned original on
14 November 2026 and made these changes:

- The theorem becomes a Prop-valued definition with the `Statement` suffix.
  All binders move inside the proposition in the same order, with the same
  binder kinds and the source's universe-zero `Type`. The proof is omitted
  for the separate proof phase.
- The unreferenced hypothesis `hnorm` becomes an unnamed implication
  premise in its source position.
- The namespace `LocalClassFieldTheory` gets the `Langlands.NYLL` prefix.
  Published names are written in full where the source relies on its `open`
  lines, which are omitted.
- The source imports (`Mathlib.FieldTheory.Galois.Basic` and the NYLL
  `EmbeddedFrobeniusTransport` module) are replaced by
  `Mathlib.FieldTheory.IsSepClosed` and the five published modules listed
  above.
- The `noncomputable section` and all other declarations of the source file
  are omitted. A proposition definition needs no noncomputable section.

The original docstring is kept on the definition. No instance or simp
attribute is installed. No shared draft or other worker's unpublished work
was reused.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance, and the Apache-2.0
notice, followed by a dated modification record. The existing
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Scope

This unit contains only this statement. Its truth proof belongs to a separate
proof unit published after the statement is accepted and after the proof of
M276.008 is in the Library. The theorem
`abstractFixedFieldNormResidueSymbol_eq_of_primeNorm` (M283.011, line 407
onward) and all other M283 rows are separate units.
