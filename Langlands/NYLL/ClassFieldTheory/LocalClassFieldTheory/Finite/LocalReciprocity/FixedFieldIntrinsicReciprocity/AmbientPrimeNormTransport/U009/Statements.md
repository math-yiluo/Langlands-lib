# Relative norms from the intrinsic base to a fixed field: statement

This module defines one closed proposition,
`Langlands.NYLL.LocalClassFieldTheory.relativeNorm_intrinsicAbstractBase_abstractFixedFieldUnitStatement : Prop`,
the statement phase of source row M283.009, the theorem
`LocalClassFieldTheory.relativeNorm_intrinsicAbstractBase_abstractFixedFieldUnit`.
The module contains no proof. A separate proof child will prove it under the
name
`Langlands.NYLL.LocalClassFieldTheory.relativeNorm_intrinsicAbstractBase_abstractFixedFieldUnit`.

## Complete closed telescope

The source theorem has no section variables; its binders are its own. The
statement quantifies them in the source order, with the same binder kinds
and the source's universe-zero `Type`. Its body is

```lean
∀ (F : Type) [Field F]
  (S : ClosedSubgroup Gal(SeparableClosure F/F))
  (hSB : S.toSubgroup ≤ (intrinsicAbstractBase F).toSubgroup)
  [Finite
    ((intrinsicAbstractBase F).toSubgroup ⧸
      Langlands.NYLL.CyclicCohomology.extensionSubgroup
        (intrinsicAbstractBase F) S hSB)]
  [FiniteDimensional F
    (abstractFixedField F (SeparableClosure F) S)]
  (p : (abstractFixedField F (SeparableClosure F) S)ˣ),
  Langlands.NYLL.ClassFormation.relativeNorm (intrinsicAbsoluteUnits F)
      (intrinsicAbstractBase F) S hSB
      (abstractFixedFieldUnitsEquivGaloisFixed
        F (SeparableClosure F) S (Additive.ofMul p)) =
    baseUnitsEquivGaloisAmbientFixed F (SeparableClosure F)
      (Additive.ofMul
        (Langlands.NYLL.LocalFieldTheory.normUnits F
          (abstractFixedField F (SeparableClosure F) S) p))
```

(the unqualified names are in `Langlands.NYLL.LocalClassFieldTheory`, the
namespace of the definition). The hypothesis `hSB` is named in the source and
is used in the conclusion, so it keeps its name. The finiteness and
finite-dimensionality instance binders are anonymous in the source and stay
anonymous. The objects built from `abstractFixedField F (SeparableClosure F) S`
and the two unit equivalences need `[IsGalois F (SeparableClosure F)]`; as in
the source, instance search finds Mathlib's Galois instance for the separable
closure, so no Galois binder appears.

The compiled declaration was checked with `#print` (Lean v4.34.0): it is a
`def` of type `Prop` whose body is the proposition above.

## Meaning

Let `F` be a field with chosen separable closure `F^sep`, and let `S` be a
closed subgroup of `Gal(F^sep/F)`. Write `F^sep_S` for
`abstractFixedField F (SeparableClosure F) S`, the fixed field of `S` as an
intermediate field of `F^sep/F`.

- `intrinsicAbstractBase F` is the closed fixing subgroup of the bottom
  intermediate field `⊥`, that is, the whole group `Gal(F^sep/F)` presented as
  a closed subgroup. The premise `hSB` says that `S` lies in it. The first
  instance premise says that `S` has finite index in it, and the second says
  that `F^sep_S` is finite-dimensional over `F`.
- `intrinsicAbsoluteUnits F` is `galoisAmbientUnitsRep F (SeparableClosure F)`,
  the representation of `Gal(F^sep/F)` on `(F^sep)ˣ`, written additively.
- `abstractFixedFieldUnitsEquivGaloisFixed F (SeparableClosure F) S`
  identifies `Additive (F^sep_S)ˣ` with the `S`-fixed vectors of that
  representation.
- `baseUnitsEquivGaloisAmbientFixed F (SeparableClosure F)` identifies
  `Additive Fˣ` with the vectors fixed by `intrinsicAbstractBase F`, through
  `F ≃ ⊥`.
- `relativeNorm A K S hSB` is the class-formation norm from `S`-fixed to
  `K`-fixed vectors of `A`: the sum, over a system of representatives of the
  left cosets of `S` in `K`, of their actions, that is the product of the
  conjugates for `A = (F^sep)ˣ`.
- `normUnits F (F^sep_S)` is `Units.map (Algebra.norm F)`, the field norm on
  units.

So the statement says: for every unit `p` of the finite extension `F^sep_S`
of `F`, the class-formation relative norm of `p`, viewed as an `S`-fixed unit
of `F^sep`, from `S` up to the whole absolute Galois group, is the field norm
`N_{F^sep_S/F}(p)`, viewed as a unit fixed by the whole group.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M024.009, `ClassFormation.relativeNorm` | `Langlands.NYLL.ClassFormation.relativeNorm`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions` |
| M004.002, `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup`, module `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions` |
| M091.002, `LocalClassFieldTheory.intrinsicAbsoluteUnits` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbsoluteUnits`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions` |
| M091.003, `LocalClassFieldTheory.intrinsicAbstractBase` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase`, same module |
| M101.001, `LocalClassFieldTheory.abstractFixedFieldUnitsEquivGaloisFixed` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldUnitsEquivGaloisFixed`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Initial.Definitions` |
| M099.001, `LocalClassFieldTheory.abstractFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField`, reached through the previous module |
| M096.001, `LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed` | `Langlands.NYLL.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.Definitions` |
| M092.002, `LocalFieldTheory.normUnits` | `Langlands.NYLL.LocalFieldTheory.normUnits`, module `Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions` |
| Mathlib `SeparableClosure` and its `IsGalois` instance, `ClosedSubgroup`, `Finite`, `FiniteDimensional`, `Additive` | Used unchanged; `SeparableClosure` reaches the statement through the `IntrinsicAbsoluteData` module, which imports `Mathlib.FieldTheory.IsSepClosed` |

The published `relativeNorm` asks for
`[Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]`; the
reducible abbreviation `extensionSubgroup K L hLK` has this body, so instance
search finds the finiteness premise. The abbreviation `intrinsicAbsoluteUnits F`
unfolds to `galoisAmbientUnitsRep F (SeparableClosure F)` and
`intrinsicAbstractBase F` to
`closedFixingSubgroup F (SeparableClosure F) ⊥`, so both sides of the equation
lie in the same fixed subgroup, as in the source.

## Library search

The whole Library at commit `4f4af6baed8c8e029e87c8303ea44c8f1d9f2f86`
was searched for `relativeNorm_intrinsicAbstractBase`,
`intrinsicAbstractBase_abstractFixedFieldUnit`, and for uses of
`intrinsicAbsoluteUnits` and `baseUnitsEquivGaloisAmbientFixed`. The name
occurs only in the planning note `notes/reuse/nyll-public-port/m270-m288.md`.
`intrinsicAbsoluteUnits` is used only in its own module and in
`ConcreteReciprocityTransport/Initial/Definitions`, and
`baseUnitsEquivGaloisAmbientFixed` only in its own `SeparableUnitsNorm/BaseUnits`
modules, whose statements concern the values of the equivalence and of coset
actions, not relative norms of fixed-field units. The source theorems the
proof uses, `relativeNorm_intermediateFieldUnit_of_isSeparable` (M165.010) and
`relativeNorm_coe_eq_of_closedSubgroup_eq` (M166.001), are planned in
`notes/reuse/nyll-public-port/m145-m168.md` and are not in the Library. So
nothing in the Library already covers M283.009.

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
| M283.009, `LocalClassFieldTheory.relativeNorm_intrinsicAbstractBase_abstractFixedFieldUnit` | docstring 275–277, signature 278–296, proof 297–342 (omitted) | `Langlands.NYLL.LocalClassFieldTheory.relativeNorm_intrinsicAbstractBase_abstractFixedFieldUnitStatement` |

The source proof (omitted here) replaces `S` by the closed fixing subgroup of
its fixed field, using `closedFixingSubgroup_abstractFixedField_eq`, and
transports the relative norm along that equality with
`relativeNorm_coe_eq_of_closedSubgroup_eq` (source row M166.001). It then
applies `relativeNorm_intermediateFieldUnit_of_isSeparable` (source row
M165.010) to the fixed field. The proof phase therefore needs the published
proofs of M165.010 and M166.001.

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
- The namespace `LocalClassFieldTheory` gets the `Langlands.NYLL` prefix.
  Published names are written in full where the source relies on its `open`
  lines, which are omitted.
- The source imports (`Mathlib.FieldTheory.Galois.Basic` and the NYLL
  `EmbeddedFrobeniusTransport` module) are replaced by the six published
  modules listed above.
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
proof unit published after the statement is accepted and after the proofs of
M165.010 and M166.001 are in the Library. The theorem
`relativeNorm_preimage_abstractRelativeFixedFieldUnit` (M283.010, line 344
onward) and all other M283 rows are separate units.
