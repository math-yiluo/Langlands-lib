# Cosets of a relative fixing subgroup as field embeddings: definition

This module defines one declaration,
`Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom`.
It adapts source row M276.002, the definition
`LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom`, keeping the
source section variables, docstring and body unchanged. The body contains
the source's proof that the map is well defined on cosets. The definition
installs no instance and proves no separate theorem.

## Telescope

The source declares the section variables

```lean
variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsSepClosed Ω]
```

and the adapted module repeats this line. Lean includes in a definition
only the section variables that it uses, together with instance arguments
that it uses. Inspection of the compiled declaration (`#check`, Lean
v4.34.0) gives the telescope

```lean
abstractFixedFieldCosetToAlgHom :
  (k Ω : Type) → [Field k] → [Field Ω] → [Algebra k Ω] → [IsGalois k Ω] →
  (K L : ClosedSubgroup Gal(Ω/k)) → (hLK : L.toSubgroup ≤ K.toSubgroup) →
  K.toSubgroup ⧸ extensionSubgroup K L hLK →
    (abstractRelativeFixedField k Ω hLK →ₐ[abstractFixedField k Ω K] Ω)
```

The variable `[IsSepClosed Ω]` is not used by this definition, so it is not
a parameter. This agrees with the source, whose next declaration
`abstractFixedFieldCosetToAlgHom_mk` (line 78) applies the definition after
`omit [IsSepClosed Ω] in`. The source uses the same `variable` line under
Lean v4.35.0-rc2, whose rule for including section variables is the same.

| Parameter | Kind and meaning |
| --- | --- |
| `k Ω : Type` | Explicit field types, in universe zero as in the source |
| `[Field k] [Field Ω] [Algebra k Ω]` | `Ω` is a field extension of `k` |
| `[IsGalois k Ω]` | `Ω / k` is Galois; needed by `abstractSubgroupEquivGaloisGroup` |
| `K L : ClosedSubgroup Gal(Ω/k)` | Explicit closed subgroups of the Galois group |
| `hLK : L.toSubgroup ≤ K.toSubgroup` | Explicit inclusion `L ≤ K` |

## Meaning

Write `Ω^K` for `abstractFixedField k Ω K`, the fixed field of `K` as an
intermediate field of `Ω / k`, and similarly `Ω^L`. Since `L ≤ K`, `Ω^K` is
contained in `Ω^L`. `abstractRelativeFixedField k Ω hLK` is `Ω^L` viewed as
an intermediate field of `Ω` over `Ω^K`. `extensionSubgroup K L hLK` is `L`
viewed as a subgroup of `K` (`L.toSubgroup.subgroupOf K.toSubgroup`), and the
domain is the type of its left cosets in `K`.

The value on the coset of `σ ∈ K` is the `Ω^K`-algebra homomorphism
`Ω^L → Ω` sending `x` to `σ x`. In the Lean body,
`abstractSubgroupEquivGaloisGroup k Ω K σ` is `σ` viewed as an element of
`Gal(Ω/Ω^K)`; its `toAlgHom` is composed with the inclusion
`(abstractRelativeFixedField k Ω hLK).val : Ω^L →ₐ[Ω^K] Ω`.
`Quotient.liftOn'` descends this assignment to cosets.

The proof argument of `Quotient.liftOn'` shows that two representatives of
the same left coset give the same homomorphism. If `σ` and `τ` lie in the
same left coset, then `η = σ⁻¹ τ` lies in `L`, so `τ = σ η`. Every `x` in
`Ω^L` is fixed by `η`, so `σ x = σ (η x) = τ x`.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M004.002, `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup`, module `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions` |
| M099.001, `LocalClassFieldTheory.abstractFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions` |
| M099.007, `LocalClassFieldTheory.abstractSubgroupEquivGaloisGroup` | `Langlands.NYLL.LocalClassFieldTheory.abstractSubgroupEquivGaloisGroup`, same module |
| M099.009, `LocalClassFieldTheory.abstractRelativeFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedField`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Relative.Definitions` |
| Mathlib `ClosedSubgroup`, `IsGalois`, `IsSepClosed`, `Quotient.liftOn'`, `QuotientGroup.leftRel_apply`, `Subgroup.inclusion`, `IntermediateField.mem_fixedField_iff`, `AlgHom.ext`, `AlgEquiv.toAlgHom` | Used unchanged |

The module imports `Mathlib.FieldTheory.IsSepClosed` (for the class
`IsSepClosed` in the `variable` line), the published module defining
`extensionSubgroup`, and the published module defining
`abstractRelativeFixedField`, which imports the module defining
`abstractFixedField` and `abstractSubgroupEquivGaloisGroup`.

## Library search

The whole Library at commit `451cce4ca176c34856be86a36801b7a3b585ae77` was
searched for `abstractFixedFieldCoset`, `CosetToAlgHom`, for every use of
`abstractRelativeFixedField`, and for algebra homomorphisms
(`→ₐ[`) over `abstractFixedField` or out of a quotient by
`extensionSubgroup`. `abstractRelativeFixedField` is used only in its own
modules and in `AbstractFixedFieldUnits/{Relative,Representation}`, which
define unit equivalences with Galois-fixed vectors. No declaration maps
cosets to field embeddings. So nothing in the Library already covers
M276.002.

## Original source

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldRelativeNorm.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldRelativeNorm.lean>).
The file was read; its SHA-256 is
`ab3ee25eed6dbccd721f18245bc5f17aea6fbe8e7631a11f41e9eb88032c1e4c`.
The header is at lines 1–5, the imports at 7–10, the module docstring at
12–20, `noncomputable section` at 24, `open scoped BigOperators` at 26, the
namespace at 28, the `open` lines at 30–31 and the `variable` line at 33–34.

| Source unit and original declaration | Source lines | Adapted declaration |
| --- | --- | --- |
| M276.002, `LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom` | docstring 43–44, signature 45–50, body 50–76 | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom` |

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
- The source imports (`Mathlib.FieldTheory.Galois.Basic`,
  `Mathlib.FieldTheory.PrimitiveElement` and the NYLL modules
  `AbstractFixedFieldUnits` and `SeparableNormProduct`) are replaced by the
  three imports listed above.
- The source `open` lines are replaced by
  `open Langlands.NYLL.CyclicCohomology`, the only opened namespace whose
  names (`extensionSubgroup`) the definition uses. `open scoped BigOperators`
  is omitted because the definition has no big operators.
- The local instance `finiteSeparableAlgHomFintypeRelative` (M276.001,
  lines 36–41) is omitted. The definition does not use it.
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

This unit contains only this definition. The theorem
`abstractFixedFieldCosetToAlgHom_mk` (M276.003, line 81) and the later
declarations of the source file are separate units.
