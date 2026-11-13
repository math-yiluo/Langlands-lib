# The unit norm between two concrete fixed fields: definition

This module defines one declaration,
`Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldNormUnits`.
It adapts source row M277.004, the definition
`LocalClassFieldTheory.abstractFixedFieldNormUnits`, keeping the source
section variables, docstring and body unchanged. The definition installs no
instance and proves no theorem.

## Telescope

The source declares the section variables

```lean
variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
```

and the adapted module repeats this line. Lean includes in a definition
only the section variables that it uses, together with instance arguments
that it uses. Inspection of the compiled declaration (`#check`, Lean
v4.34.0) gives the telescope

```lean
abstractFixedFieldNormUnits :
  (k Ω : Type) → [Field k] → [Field Ω] → [Algebra k Ω] →
  (K K' : ClosedSubgroup Gal(Ω/k)) → (hK'K : K'.toSubgroup ≤ K.toSubgroup) →
  Additive (abstractRelativeFixedField k Ω hK'K)ˣ →+
    Additive (abstractFixedField k Ω K)ˣ
```

The variable `[IsGalois k Ω]` is not used: neither the published
`abstractFixedField` and `abstractRelativeFixedField` nor `normUnits` needs
it. So it is not a parameter. The source uses the same `variable` line under
Lean v4.35.0-rc2, whose rule for including section variables is the same.

| Parameter | Kind and meaning |
| --- | --- |
| `k Ω : Type` | Explicit field types, in universe zero as in the source |
| `[Field k] [Field Ω] [Algebra k Ω]` | `Ω` is a field extension of `k` |
| `K K' : ClosedSubgroup Gal(Ω/k)` | Explicit closed subgroups of the Galois group |
| `hK'K : K'.toSubgroup ≤ K.toSubgroup` | Explicit inclusion `K' ≤ K` |

## Meaning

Write `Ω^K` for `abstractFixedField k Ω K`, the fixed field of `K` as an
intermediate field of `Ω / k`, and similarly `Ω^{K'}`. Since `K' ≤ K`,
`Ω^K ⊆ Ω^{K'}`, and `abstractRelativeFixedField k Ω hK'K` is `Ω^{K'}` viewed
as an intermediate field of `Ω` over `Ω^K`. It is an `Ω^K`-algebra through
this inclusion.

The body is

```lean
MonoidHom.toAdditive
  (normUnits (abstractFixedField k Ω K)
    (abstractRelativeFixedField k Ω hK'K))
```

`Langlands.NYLL.LocalFieldTheory.normUnits F E : Eˣ →* Fˣ` is
`Units.map (Algebra.norm F)`, the field norm `N_{E/F}` restricted to unit
groups. `MonoidHom.toAdditive` writes the same homomorphism additively, as
`Additive Eˣ →+ Additive Fˣ`. So the definition is the norm
`N_{Ω^{K'}/Ω^K}` on units, written additively. No finiteness of
`Ω^{K'} / Ω^K` is assumed; `Algebra.norm` is `1` on every element when the
extension is not finite, and then so is this map.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M092.002, `LocalFieldTheory.normUnits` | `Langlands.NYLL.LocalFieldTheory.normUnits`, module `Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions` |
| M099.001, `LocalClassFieldTheory.abstractFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions`, reached through the next import |
| M099.009, `LocalClassFieldTheory.abstractRelativeFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedField`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Relative.Definitions` |
| Mathlib `ClosedSubgroup`, `IsGalois`, `Additive`, `MonoidHom.toAdditive`, `Units` | Used unchanged |

The module imports the two published modules named in the table that
define `normUnits` and `abstractRelativeFixedField`.

## Library search

The whole Library at commit `451cce4ca176c34856be86a36801b7a3b585ae77` was
searched for `abstractFixedFieldNormUnits`, for every use of `normUnits`,
for `MonoidHom.toAdditive` applied to a unit norm, and for every use of
`abstractRelativeFixedField`. Two generic unit norms exist: the reused
`Langlands.NYLL.LocalFieldTheory.normUnits` and the independent
`Langlands.LocalClassField.normUnits` in
`Langlands/ClassFieldTheory/Local/Norms.lean`, both `Units.map` of the
algebra norm. Neither is applied anywhere to `abstractFixedField` or
`abstractRelativeFixedField`; the only fixed-field uses (in
`Langlands/ClassFieldTheory/Local/InertiaFixedFieldNorm*`) concern inertia
fixed fields of local fields. `abstractRelativeFixedField` is used only in
its own modules and in `AbstractFixedFieldUnits/{Relative,Representation}`,
which define unit equivalences with Galois-fixed vectors, not norms. So
nothing in the Library already covers M277.004. The NYLL `normUnits` is
reused because the source names it.

## Original source

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean>).
The file was read; its SHA-256 is
`f05e7d0475ae6837a3a41da9e3185201178a01a78da0afc37557b9314bc42981`.
The header is at lines 1–5, the imports at 7–11, the module docstring at
13–19, `noncomputable section` at 23, the namespace at 25, the `open` lines
at 27–28 and the `variable` line at 30.

| Source unit and original declaration | Source lines | Adapted declaration |
| --- | --- | --- |
| M277.004, `LocalClassFieldTheory.abstractFixedFieldNormUnits` | docstring 97, signature 98–102, body 103–105 | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldNormUnits` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 56 extracted the definition directly from the pinned original on
13 November 2026 and made these changes:

- The namespace `LocalClassFieldTheory` gets the `Langlands.NYLL` prefix.
  The name, docstring, `variable` line, signature and body are unchanged.
- The source imports (the NYLL modules `FixedFieldRelativeNorm`,
  `LocalClassFieldAxiom`, `LocalHenselianValuation` and
  `AbstractClassFieldTheory.Reciprocity.Main`, and
  `Mathlib.FieldTheory.Galois.Notation`) are replaced by the two published
  modules listed above.
- The source `open` lines are replaced by
  `open Langlands.NYLL.LocalFieldTheory`, the only opened namespace whose
  names (`normUnits`) the definition uses.
- All other declarations of the source file are omitted.

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

This unit contains only this definition. The other declarations of the
source file, including `abstractFixedFieldUnitsInclusion` (M277.001),
`abstractFixedFieldNormResidueSymbol` (M277.003) and
`abstractFixedFieldAbelianizedRestriction` (M277.005), are separate units.
