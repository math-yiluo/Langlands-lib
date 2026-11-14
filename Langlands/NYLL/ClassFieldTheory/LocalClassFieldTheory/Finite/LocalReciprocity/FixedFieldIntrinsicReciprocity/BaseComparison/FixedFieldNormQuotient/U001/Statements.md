# Fixed-field finite norm subgroups: statement

This module defines one closed proposition,
`Langlands.NYLL.LocalClassFieldTheory.map_fixedFieldFiniteNormSubgroup_eq_additiveNormSubgroupStatement : Prop`,
the statement phase of source row M278.001, the theorem
`LocalClassFieldTheory.map_fixedFieldFiniteNormSubgroup_eq_additiveNormSubgroup`.
The module contains no proof. A separate proof child will prove it under the
name
`Langlands.NYLL.LocalClassFieldTheory.map_fixedFieldFiniteNormSubgroup_eq_additiveNormSubgroup`.

## Complete closed telescope

The source file declares no section variables before this theorem; the
theorem binds all its parameters itself. The statement quantifies them in
the source order, with the same binder kinds. Its body is

```lean
∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsSepClosed Ω]
  (K L : ClosedSubgroup Gal(Ω/k))
  (hLK : L.toSubgroup ≤ K.toSubgroup)
  [Finite
    (K.toSubgroup ⧸
      Langlands.NYLL.CyclicCohomology.extensionSubgroup K L hLK)]
  [Finite
    ((Langlands.NYLL.ClassFormation.baseField Gal(Ω/k)).toSubgroup ⧸
      Langlands.NYLL.CyclicCohomology.extensionSubgroup
        (Langlands.NYLL.ClassFormation.baseField Gal(Ω/k)) K
        (Langlands.NYLL.ClassFormation.le_baseField K))],
  (Langlands.NYLL.ClassFormation.finiteNormSubgroup
      (galoisAmbientUnitsRep k Ω) K L hLK).map
      (abstractFixedFieldUnitsEquivGaloisFixed
        k Ω K).symm.toAddMonoidHom =
    Langlands.NYLL.CyclicCohomology.additiveNormSubgroup
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK)
```

(the unqualified names are in `Langlands.NYLL.LocalClassFieldTheory`, the
namespace of the definition). The source names the two finiteness instance
binders `hfinite` and `hKabsolute`. They are used only in the omitted
proof, so here they are anonymous instance binders in the same places. The
second binder and `[IsSepClosed Ω]` are not used by the asserted equation;
they stay as premises because the source theorem has them.

## Meaning

Let `Ω / k` be Galois with `Ω` separably closed, and let `L ≤ K` be closed
subgroups of `Gal(Ω/k)`. Write `Ω^K` for `abstractFixedField k Ω K` and
`Ω^L` for `abstractRelativeFixedField k Ω hLK`, the fixed field of `L`
viewed as an `Ω^K`-algebra. The two premises say that `L` has finite index
in `K` and that `K` has finite index in the whole group
`baseField Gal(Ω/k)`, whose underlying subgroup is all of `Gal(Ω/k)`.

- `galoisAmbientUnitsRep k Ω` is the representation of `Gal(Ω/k)` on `Ωˣ`,
  written additively.
- `finiteNormSubgroup A K L hLK` is the range of the class-formation
  relative norm `relativeNorm A K L hLK` from `L`-fixed to `K`-fixed
  vectors of `A`, an additive subgroup of the `K`-fixed vectors. For
  `A = Ωˣ`, written multiplicatively, the relative norm of an `L`-fixed
  unit is the product of its conjugates over a system of representatives
  of the cosets of `L` in `K`.
- `abstractFixedFieldUnitsEquivGaloisFixed k Ω K` is the additive
  isomorphism from `Additive (Ω^K)ˣ` to the `K`-fixed vectors of
  `galoisAmbientUnitsRep k Ω`, sending a unit to itself in `Ωˣ`. The
  statement maps the subgroup by its inverse.
- `additiveNormSubgroup (Ω^K) (Ω^L)` is the subgroup
  `localNormSubgroup (Ω^K) (Ω^L)` of `(Ω^K)ˣ`, the range of
  `normUnits (Ω^K) (Ω^L) = Units.map (Algebra.norm (Ω^K))`, viewed as an
  additive subgroup of `Additive (Ω^K)ˣ`.

So the statement says: under the identification of `K`-fixed units of `Ω`
with units of `Ω^K`, the image of the class-formation norm from `L`-fixed
units is exactly the group `N_{Ω^L/Ω^K}((Ω^L)ˣ)` of field norms. No
normality of `Ω^L` over `Ω^K` is assumed.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M039.001, `ClassFormation.finiteNormSubgroup` | `Langlands.NYLL.ClassFormation.finiteNormSubgroup`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions` |
| M010.003, `ClassFormation.baseField` | `Langlands.NYLL.ClassFormation.baseField`, reached through the next module |
| M010.005, `ClassFormation.le_baseField` | `Langlands.NYLL.ClassFormation.le_baseField : le_baseFieldStatement K`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs` |
| M004.002, `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup`, module `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions` |
| M088.001, `LocalClassFieldTheory.galoisAmbientUnitsRep` | `Langlands.NYLL.LocalClassFieldTheory.galoisAmbientUnitsRep`, reached through the next module |
| M101.001, `LocalClassFieldTheory.abstractFixedFieldUnitsEquivGaloisFixed` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldUnitsEquivGaloisFixed`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Initial.Definitions` |
| M099.001, `LocalClassFieldTheory.abstractFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField`, reached through the previous module |
| M099.009, `LocalClassFieldTheory.abstractRelativeFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedField`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Relative.Definitions` |
| M095.008, `CyclicCohomology.additiveNormSubgroup` | `Langlands.NYLL.CyclicCohomology.additiveNormSubgroup`, module `Langlands.NYLL.GaloisCohomology.Cyclic.TateH0.NormImage.Definitions` |
| Mathlib `ClosedSubgroup`, `IsGalois`, `IsSepClosed`, `Finite`, `AddSubgroup.map`, `AddEquiv.toAddMonoidHom` | Used unchanged; `IsSepClosed` is imported from `Mathlib.FieldTheory.IsSepClosed` |

The published `le_baseField K` proves `le_baseFieldStatement K`, which
unfolds to `K.toSubgroup ≤ (baseField G).toSubgroup`, so it is accepted as
the inequality argument of `extensionSubgroup`, as in the source. The
published `finiteNormSubgroup` asks for
`[Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]`; the
reducible abbreviation `extensionSubgroup K L hLK` has this body, so
instance search finds the first premise.

The compiled declaration was checked with `#print` (Lean v4.34.0): it is a
`def` of type `Prop` whose body is the proposition above.

## Library search

The whole Library at commit `58ad0f796899b4aa457077d0146815c24758f739`
was searched for `map_fixedFieldFiniteNormSubgroup` and
`fixedFieldFiniteNormQuotient`, for every use of `finiteNormSubgroup`, of
`additiveNormSubgroup` and of `abstractFixedFieldUnitsEquivGaloisFixed`,
and for uses of `localNormSubgroup`. The names occur only in the planning
note `notes/reuse/nyll-public-port/m270-m288.md`. `finiteNormSubgroup` and
`additiveNormSubgroup` are used only in their own modules
(`Reciprocity/Construction/FiniteNormQuotient` and `Cyclic/TateH0/NormImage`).
The fixed-unit equivalence is used only in the `AbstractFixedFieldUnits`
modules and in the statement `NormSubgroupOrderEmbedding/U006`, which
computes the relative norm from the whole group for the intrinsic
separable closure, not the norm subgroup between two fixed fields. The NYLL
`NormQuotient` modules use `localNormSubgroup` for local fields without
class-formation norms, and the independent
`Langlands/ClassFieldTheory/Local/Norms.lean` defines its own norm groups
without the NYLL coefficient modules. So nothing in the Library already
covers M278.001.

## Original source

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/FixedFieldNormQuotient.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/FixedFieldNormQuotient.lean>).
The file was read; its SHA-256 is
`d64f865a72b32e672830e401a80f697fee85d344277a3fb6f5cf30f744727217`.
The header is at lines 1–5, the imports at 7–10, the module docstring at
12–17, `noncomputable section` at 21, the namespace at 23 and the `open`
lines at 25–27.

| Source unit and original declaration | Source lines | Adapted declaration |
| --- | --- | --- |
| M278.001, `LocalClassFieldTheory.map_fixedFieldFiniteNormSubgroup_eq_additiveNormSubgroup` | docstring 29–30, signature 31–47, proof 48–94 (omitted) | `Langlands.NYLL.LocalClassFieldTheory.map_fixedFieldFiniteNormSubgroup_eq_additiveNormSubgroupStatement` |

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
  suffix. Its complete telescope moves inside the proposition in the same
  order and with the same binder kinds and the source's universe-zero
  `Type`. The named instance binders `hfinite` and `hKabsolute` become
  anonymous instance binders. The proof is omitted for the separate proof
  phase.
- The name keeps the source name with the `Langlands.NYLL` prefix and the
  `Statement` suffix; the source docstring is kept.
- Published names are written in full where the source relies on its
  `open` lines.
- The source imports (`Mathlib.FieldTheory.Galois.Basic` and the NYLL
  modules `EmbeddedInertiaComparison`, `FixedFieldNormResidueNaturality`
  and `NonarchimedeanLocalField.NormQuotient`) are replaced by
  `Mathlib.FieldTheory.IsSepClosed` and the six published modules listed
  above.
- The definition M278.002, the theorems M278.003–M278.006 and all other
  declarations of the source file are omitted.

No instance or simp attribute is installed. No shared draft or other
worker's unpublished work was reused.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance, and the Apache-2.0
notice, followed by a dated modification record. The existing
[LICENSE](../../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../../licenses/NYLL/NOTICE) match the
pinned upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Scope

This unit contains only this statement. Its truth proof belongs to a
separate proof unit published after the statement is accepted. The source
proof uses `abstractRelativeFixedField_finiteDimensional` (M099.019),
`abstractRelativeFixedFieldUnitsEquivGaloisFixed` (M101.003) and the
theorem `relativeNorm_abstractFixedFieldUnit_eq_normUnits` (M276.008).
