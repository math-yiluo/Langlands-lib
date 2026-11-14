# Relative cosets are the embeddings of a finite fixed field: definition

This module defines one declaration,
`Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldCosetEquivAlgHom`.
It adapts source row M276.006, the definition
`LocalClassFieldTheory.abstractFixedFieldCosetEquivAlgHom`, keeping the
source section variables, docstring, signature and body. The body cites the
two private source theorems by their published names. The definition
installs no instance and proves no separate theorem.

## Telescope

The source declares the section variables

```lean
variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsSepClosed Ω]
```

and the adapted module repeats this line. Inspection of the compiled
declaration (`#check`, Lean v4.34.0) gives the telescope

```lean
abstractFixedFieldCosetEquivAlgHom :
  (k Ω : Type) → [Field k] → [Field Ω] → [Algebra k Ω] →
  [IsGalois k Ω] → [IsSepClosed Ω] →
  (K L : ClosedSubgroup Gal(Ω/k)) → (hLK : L.toSubgroup ≤ K.toSubgroup) →
  [FiniteDimensional (abstractFixedField k Ω K)
    (abstractRelativeFixedField k Ω hLK)] →
  K.toSubgroup ⧸ extensionSubgroup K L hLK ≃
    (abstractRelativeFixedField k Ω hLK →ₐ[abstractFixedField k Ω K] Ω)
```

Both instance variables are used: `[IsGalois k Ω]` by the coset map and
both theorems, `[IsSepClosed Ω]` by the surjectivity theorem. The source
uses the same `variable` line under Lean v4.35.0-rc2, whose rule for
including section variables is the same.

## Meaning

Write `Ω^K ⊆ Ω^L` for the fixed fields of closed subgroups `L ≤ K` of
`Gal(Ω/k)`, where `Ω / k` is Galois and `Ω` is separably closed, and assume
`Ω^L` is finite over `Ω^K`. The body is

```lean
Equiv.ofBijective (abstractFixedFieldCosetToAlgHom k Ω K L hLK)
  ⟨Langlands.NYLL.PortInternal.M276.d005 k Ω K L hLK,
    Langlands.NYLL.PortInternal.M276.d004 k Ω K L hLK⟩
```

`abstractFixedFieldCosetToAlgHom` (M276.002) sends the left coset of
`σ ∈ K` modulo `L` to the embedding `x ↦ σ x` of `Ω^L` into `Ω` over `Ω^K`.
The published theorems `d005` (M276.005) and `d004` (M276.004) prove that
this map is injective and, under the finiteness instance, surjective.
`Equiv.ofBijective` packages it as an equivalence whose forward function is
exactly `abstractFixedFieldCosetToAlgHom k Ω K L hLK`. So the definition
identifies `K / L` with the set of `Ω^K`-embeddings of `Ω^L` into `Ω`.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M276.002, `LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U002.Definitions`, reached through the imports |
| M276.004, private `LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom_surjective` | `Langlands.NYLL.PortInternal.M276.d004 : d004Statement`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U004.Proofs` |
| M276.005, private `LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom_injective` | `Langlands.NYLL.PortInternal.M276.d005 : d005Statement`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U005.Proofs` |
| M004.002, M099.001, M099.009, `extensionSubgroup`, `abstractFixedField`, `abstractRelativeFixedField` | The published `Langlands.NYLL` declarations, reached through the imports |
| Mathlib `Equiv.ofBijective`, `ClosedSubgroup`, `IsGalois`, `IsSepClosed`, `FiniteDimensional` | Used unchanged |

The published theorems prove closed propositions whose binders are, in
order, those of the source theorems. Applied to `k Ω K L hLK`, with the
instance arguments found by instance search, they give exactly the source
terms `abstractFixedFieldCosetToAlgHom_injective k Ω K L hLK` and
`abstractFixedFieldCosetToAlgHom_surjective k Ω K L hLK`.

## Library search

The whole Library at commit `457e31a2131a1083c26931d33fec09a71fea54d6` was
searched for `abstractFixedFieldCosetEquivAlgHom`, `CosetEquivAlgHom`, and
for `Equiv.ofBijective` applied to a coset map into an `→ₐ[` type. None
occurs; the only coset-to-embedding map is the published M276.002 unit,
used here. So nothing in the Library already covers M276.006.

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
| M276.006, `LocalClassFieldTheory.abstractFixedFieldCosetEquivAlgHom` | docstring 157–158, signature 159–166, body 167–169 | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldCosetEquivAlgHom` |

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
  The name, docstring, `variable` line and signature are unchanged.
- In the body, the private source theorems
  `abstractFixedFieldCosetToAlgHom_injective` and
  `abstractFixedFieldCosetToAlgHom_surjective` are replaced by their
  published adaptations `Langlands.NYLL.PortInternal.M276.d005` and
  `Langlands.NYLL.PortInternal.M276.d004`, applied to the same arguments.
- The source imports are replaced by the two published proof modules,
  which import everything else used.
- The source `open` lines are replaced by
  `open Langlands.NYLL.CyclicCohomology` (for `extensionSubgroup`).
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
`relativeNorm_abstractFixedFieldUnit_eq_normUnits` (M276.008, line 192),
whose proof uses it, is a separate unit.
