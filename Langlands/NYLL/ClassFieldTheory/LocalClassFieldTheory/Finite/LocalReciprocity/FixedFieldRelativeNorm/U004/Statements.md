# Cosets as field embeddings: bijectivity and the coset action, statements

This module defines three closed propositions:

- `Langlands.NYLL.PortInternal.M276.d004Statement : Prop`, the statement
  phase of source row M276.004, the private theorem
  `LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom_surjective`;
- `Langlands.NYLL.PortInternal.M276.d005Statement : Prop`, the statement
  phase of source row M276.005, the private theorem
  `LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom_injective`;
- `Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_abstractFixedFieldUnit_valStatement : Prop`,
  the statement phase of source row M276.007, the theorem
  `LocalClassFieldTheory.relativeCosetAction_abstractFixedFieldUnit_val`.

The module contains no proof. Separate proof children will prove them under
the names `Langlands.NYLL.PortInternal.M276.d004`,
`Langlands.NYLL.PortInternal.M276.d005` and
`Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_abstractFixedFieldUnit_val`.
The two source theorems are `private`, so, as for other private NYLL
theorems in the Library, they are named by their source rows in the
namespace `Langlands.NYLL.PortInternal.M276`.

## Common notation

All three take fields `k Ω : Type` with `[Field k] [Field Ω] [Algebra k Ω]`
and `[IsGalois k Ω]`, closed subgroups `K L : ClosedSubgroup Gal(Ω/k)` and
`hLK : L.toSubgroup ≤ K.toSubgroup`. Write `Ω^K` for
`abstractFixedField k Ω K` (the fixed field of `K`), `Ω^L` for
`abstractRelativeFixedField k Ω hLK` (the fixed field of `L`, viewed over
`Ω^K`), and `Q` for the left-coset type
`K.toSubgroup ⧸ extensionSubgroup K L hLK`. The published definition
`abstractFixedFieldCosetToAlgHom k Ω K L hLK : Q → (Ω^L →ₐ[Ω^K] Ω)` (M276.002)
sends the coset of `σ ∈ K` to the embedding `x ↦ σ x`.

## Complete closed telescopes

The source declares the section variables
`(k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] [IsSepClosed Ω]`.
A theorem includes every instance section variable whose types mention only
included variables, unless it is omitted. M276.004 therefore has both
`[IsGalois k Ω]` and `[IsSepClosed Ω]`; M276.005 and M276.007 follow
`omit [IsSepClosed Ω] in` and have only `[IsGalois k Ω]`. The statements
quantify exactly these binders, in the source order.

The body of `d004Statement` is

```lean
∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsSepClosed Ω]
  (K L : ClosedSubgroup (Gal(Ω/k)))
  (hLK : L.toSubgroup ≤ K.toSubgroup)
  [FiniteDimensional
    (Langlands.NYLL.LocalClassFieldTheory.abstractFixedField k Ω K)
    (Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedField
      k Ω hLK)],
  Function.Surjective
    (Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom
      k Ω K L hLK)
```

It says: if `Ω` is separably closed and `Ω^L` is finite-dimensional over
`Ω^K`, every `Ω^K`-embedding of `Ω^L` into `Ω` is `x ↦ σ x` for some
`σ ∈ K`.

The body of `d005Statement` is

```lean
∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω]
  (K L : ClosedSubgroup (Gal(Ω/k)))
  (hLK : L.toSubgroup ≤ K.toSubgroup),
  Function.Injective
    (Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom
      k Ω K L hLK)
```

It says: if `σ, τ ∈ K` agree on `Ω^L`, they lie in the same left coset of
`L`.

The body of `relativeCosetAction_abstractFixedFieldUnit_valStatement` is

```lean
∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω]
  (K L : ClosedSubgroup (Gal(Ω/k)))
  (hLK : L.toSubgroup ≤ K.toSubgroup)
  (x : (abstractRelativeFixedField k Ω hLK)ˣ)
  (q : K.toSubgroup ⧸
    Langlands.NYLL.CyclicCohomology.extensionSubgroup K L hLK),
  ((Additive.toMul
    (Langlands.NYLL.ClassFormation.relativeCosetAction
      (galoisAmbientUnitsRep k Ω)
      K L hLK
      (abstractRelativeFixedFieldUnitsEquivGaloisFixed
        k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω) =
    abstractFixedFieldCosetToAlgHom k Ω K L hLK q
      (x : abstractRelativeFixedField k Ω hLK)
```

(the unqualified names are in `Langlands.NYLL.LocalClassFieldTheory`, the
namespace of the definition). Here `galoisAmbientUnitsRep k Ω` is the
Galois representation on `Ωˣ` written additively,
`abstractRelativeFixedFieldUnitsEquivGaloisFixed k Ω K L hLK` identifies
`Additive (Ω^L)ˣ` with the `L`-fixed vectors of that representation, and
`relativeCosetAction A K L hLK a q` evaluates the action of a
representative of `q` on the `L`-fixed vector `a`. The statement says: for
a unit `x` of `Ω^L` and a coset `q` of `σ`, acting by `σ` on `x` (as a
fixed unit of `Ω`) gives the element `σ x` of `Ω`, the value at `x` of the
embedding attached to `q`. The coercions turn the additive unit back into
an element of `Ω`.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M276.002, `LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U002.Definitions` |
| M004.002, `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup`, reached through the M276.002 module |
| M099.001 / M099.009, `abstractFixedField` / `abstractRelativeFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField`, `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedField`, reached through the M276.002 module |
| M024.001, `ClassFormation.relativeCosetAction` | `Langlands.NYLL.ClassFormation.relativeCosetAction`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Definitions` |
| M088.001, `LocalClassFieldTheory.galoisAmbientUnitsRep` | `Langlands.NYLL.LocalClassFieldTheory.galoisAmbientUnitsRep`, reached through the next module |
| M101.003, `LocalClassFieldTheory.abstractRelativeFixedFieldUnitsEquivGaloisFixed` | `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedFieldUnitsEquivGaloisFixed`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Relative.Definitions` |
| Mathlib `ClosedSubgroup`, `IsGalois`, `IsSepClosed`, `FiniteDimensional`, `Function.Surjective`, `Function.Injective`, `Additive` | Used unchanged |

The published `relativeCosetAction` writes its coset argument as
`K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup`, the body of the
reducible abbreviation `extensionSubgroup K L hLK`, so the source's `q`
is accepted unchanged.

## Library search

The whole Library at commit `4bd8ef92a8f330864b325814d41cb38bf51b7794` was
searched for `abstractFixedFieldCosetToAlgHom`, for
`relativeCosetAction_abstractFixedFieldUnit`, for the namespace
`Langlands.NYLL.PortInternal.M276`, and for `relativeCosetAction` together
with `abstractRelativeFixedFieldUnitsEquivGaloisFixed`. The coset
embedding is not yet in the Library (its definition is the separate,
staged M276.002 unit), and the namespace `PortInternal.M276` does not
exist. The NYLL `relativeCosetAction` is used only for abstract
representations, in the class-formation modules `Degree/Norm` and
`Reciprocity/FieldRepresentation/Action`; the independent lemma
`relativeCosetAction_baseUnit` in
`Langlands/ClassFieldTheory/Local/NormExistenceNormTransfer.lean` concerns
base units of normal extensions of local fields. None relates the coset
action to field embeddings of fixed fields. So nothing in the Library
already covers M276.004, M276.005 or M276.007.

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
| M276.004, private `abstractFixedFieldCosetToAlgHom_surjective` | signature 90–96, proof 96–126 (omitted) | `Langlands.NYLL.PortInternal.M276.d004Statement` |
| M276.005, private `abstractFixedFieldCosetToAlgHom_injective` | `omit` 128, signature 129–133, proof 133–155 (omitted) | `Langlands.NYLL.PortInternal.M276.d005Statement` |
| M276.007, `relativeCosetAction_abstractFixedFieldUnit_val` | `omit` 171, docstring 172, signature 173–184, proof 184–187 (omitted) | `Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_abstractFixedFieldUnit_valStatement` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 56 extracted the asserted types directly from the pinned original on
13 November 2026 and made these changes:

- Each theorem becomes a Prop-valued definition with the `Statement`
  suffix. Its complete telescope, including the section variables the
  theorem uses, moves inside the proposition in the same order and with the
  same binder kinds and the source's universe-zero `Type`. The proofs are
  omitted for the separate proof phase.
- The private theorems M276.004 and M276.005 are named `d004Statement` and
  `d005Statement` in `Langlands.NYLL.PortInternal.M276`; they have no
  source docstring, so the adapted docstrings describe them. M276.007 keeps
  its source name, with the `Langlands.NYLL` prefix, and its docstring.
- Published names are written in full where the source relies on its
  `open` lines.
- The source imports are replaced by the three published modules listed
  above.
- The local instance M276.001, the definitions M276.002 and M276.006, the
  theorems M276.003 and M276.008 and all other declarations of the source
  file are omitted.

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

This unit contains only these three statements. Their truth proofs belong
to separate proof units published after the statements are accepted, one
per statement.
