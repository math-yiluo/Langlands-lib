# Cosets of the base fixing subgroup as embeddings: surjectivity and injectivity targets (M165.003, M165.004)

Let `Ω / K` be a Galois extension and `E` an intermediate field. The map
`Langlands.NYLL.LocalClassFieldTheory.baseFixingCosetToAlgHom K Ω E`
(source unit M165.001, sibling module `Definitions`) sends the left coset
`σ · Gal(Ω / E)` of an automorphism `σ ∈ Gal(Ω / K)` to the restriction
`σ|_E : E → Ω`, a `K`-algebra homomorphism. This module defines two
propositions about that map:

- `Langlands.NYLL.PortInternal.M165.d003Statement K Ω E` (source unit
  M165.003): if `Ω` is separably closed and `E / K` is finite and separable,
  the map is surjective. Every `K`-embedding of `E` into `Ω` is the
  restriction of an automorphism of `Ω / K`.
- `Langlands.NYLL.PortInternal.M165.d004Statement K Ω E` (source unit
  M165.004): the map is injective. Two left cosets with the same restriction
  to `E` are equal. No separable-closedness or finiteness is assumed.

In Lean:

```lean
namespace Langlands.NYLL.LocalClassFieldTheory

def _root_.Langlands.NYLL.PortInternal.M165.d003Statement
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsSepClosed Ω]
    (E : IntermediateField K Ω)
    [FiniteDimensional K E] [Algebra.IsSeparable K E] : Prop :=
  Function.Surjective (baseFixingCosetToAlgHom K Ω E)

def _root_.Langlands.NYLL.PortInternal.M165.d004Statement
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω]
    (E : IntermediateField K Ω) : Prop :=
  Function.Injective (baseFixingCosetToAlgHom K Ω E)
```

Defining the propositions does not prove them.

## Parameters and meaning

| Binder | Kind | In `d003Statement` | In `d004Statement` | Meaning |
| --- | --- | --- | --- | --- |
| `K`, `Ω` | explicit, `Type` | yes | yes | Base field and ambient field (universe 0, as in the source) |
| `[Field K]`, `[Field Ω]`, `[Algebra K Ω]` | instance-implicit | yes | yes | `Ω` is a field extension of `K` |
| `[IsGalois K Ω]` | instance-implicit | yes | yes | `Ω / K` is Galois (Mathlib's `IsGalois`: normal and separable, not necessarily finite) |
| `[IsSepClosed Ω]` | instance-implicit | yes | no | `Ω` is separably closed |
| `E` | explicit, `IntermediateField K Ω` | yes | yes | The intermediate field |
| `[FiniteDimensional K E]` | instance-implicit | yes | no | `E / K` is finite |
| `[Algebra.IsSeparable K E]` | instance-implicit | yes | no | `E / K` is separable |

The domain of `baseFixingCosetToAlgHom K Ω E` is the quotient of the subgroup
`(closedFixingSubgroup K Ω ⊥).toSubgroup` of `Gal(Ω / K)` (which, as a set, is
all of `Gal(Ω / K)`, since every automorphism fixes `⊥`) by its subgroup
`extensionSubgroup (closedFixingSubgroup K Ω ⊥) (closedFixingSubgroup K Ω E)
(fixingSubgroupLeBase K Ω E)`, which is `Gal(Ω / E)`. Its elements are left
cosets. The codomain is `E →ₐ[K] Ω`. `Function.Surjective` and
`Function.Injective` are the core Lean predicates. The paired Markdown of the
`Definitions` module describes the map and its published ingredients
`closedFixingSubgroup` (M087.001), `extensionSubgroup` (M004.002) and
`fixingSubgroupLeBase` (M089.002).

The map itself takes no `IsSepClosed` argument (see the `Definitions`
Markdown). The hypotheses `[IsSepClosed Ω]`, `[FiniteDimensional K E]` and
`[Algebra.IsSeparable K E]` of `d003Statement` are hypotheses of the source
theorem, used by its proof through Mathlib's
`IsSepClosed.surjective_domRestrict_of_isSeparable`; the map does not consume
them. The target keeps all three, so it states exactly the source result and
nothing stronger.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean),
SHA-256 `477273f35f3c5945fe5ccb5cb38e4527f2656e8f3f2ef85451aef32c639e4106`.
The relevant lines are:

- the section variables at lines 36–37,
  `variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]`,
  and at line 41 inside `section CosetsAndEmbeddings` (line 39),
  `variable (E : IntermediateField K Ω)`;
- M165.003: statement at lines 91–93, proof at lines 93–117;
- M165.004: `omit [IsSepClosed Ω] in` at line 119, statement at lines
  120–121, proof at lines 121–139.

The source statements are:

```lean
private theorem baseFixingCosetToAlgHom_surjective
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    Function.Surjective (baseFixingCosetToAlgHom K Ω E) := by

omit [IsSepClosed Ω] in
private theorem baseFixingCosetToAlgHom_injective :
    Function.Injective (baseFixingCosetToAlgHom K Ω E) := by
```

Both are `private` and have no docstring. A Lean theorem takes every section
variable that its statement mentions, together with every instance-implicit
section variable whose own variables are all taken. So the source surjectivity
theorem takes `K`, `Ω`, `[Field K]`, `[Field Ω]`, `[Algebra K Ω]`,
`[IsGalois K Ω]`, `[IsSepClosed Ω]` and `E`, followed by its own two
instance arguments. The injectivity theorem takes the same arguments except
the omitted `[IsSepClosed Ω]`. The two definitions above list exactly these
binders, in this order, with the same binder kinds and names.

The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution is also registered
as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Library's `notes/errata/` has no NYLL entry.

| Original declaration | Adapted declaration |
| --- | --- |
| private `LocalClassFieldTheory.baseFixingCosetToAlgHom_surjective` (M165.003) | `Langlands.NYLL.PortInternal.M165.d003Statement` (target) |
| private `LocalClassFieldTheory.baseFixingCosetToAlgHom_injective` (M165.004) | `Langlands.NYLL.PortInternal.M165.d004Statement` (target) |
| `LocalClassFieldTheory.baseFixingCosetToAlgHom` (M165.001, used) | `Langlands.NYLL.LocalClassFieldTheory.baseFixingCosetToAlgHom` (sibling module `Definitions`) |

Rows M165.003 and M165.004 of the published partition
[`notes/reuse/nyll-public-port/m145-m168.md`](../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md)
reserve `Langlands.NYLL.PortInternal.M165.d003` and
`Langlands.NYLL.PortInternal.M165.d004` for these private theorems. Section
"Names and separate phases" of
[`notes/reuse/nyll-public-port-plan.md`](../../../../../../../../notes/reuse/nyll-public-port-plan.md)
adds `Statement` for a theorem's target. These are fresh names, not the
compiler's names for the private originals. No declaration of either name
exists in the current Library or Mathlib.

## Imports and modification record

The only import is the sibling module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.Initial.Definitions`,
which defines `baseFixingCosetToAlgHom` and, through its imports, supplies
Mathlib's `IsGalois`, `IsSepClosed`, `IntermediateField`,
`FiniteDimensional` and `Algebra.IsSeparable`. The source's two NYLL imports
are replaced by it. Every transitive import lies in the approved Mathlib
environment or the published Library.

Worker 85 extracted these two statements on 13 November 2026. The Lean header
records the change. The changes are:

- each private theorem becomes a public Prop-valued definition with the
  reserved `PortInternal` name and the `Statement` suffix;
- the section variables that the theorem takes are written as explicit binders
  of the definition, in the source order. A definition, unlike a theorem,
  drops section variables that its body does not use. Written as section
  variables, `[IsSepClosed Ω]`, `[FiniteDimensional K E]` and
  `[Algebra.IsSeparable K E]` would therefore disappear from `d003Statement`,
  leaving a proposition with fewer hypotheses than the source theorem. Binders
  written in the header are always kept;
- the definitions are declared with `_root_` inside the namespace
  `Langlands.NYLL.LocalClassFieldTheory`, so that `baseFixingCosetToAlgHom`
  resolves to the adapted definition, following the published precedent
  `Langlands.NYLL.PortInternal.M066.d013Statement`;
- each definition has a new docstring, since the source theorems have none;
- the proofs and every other declaration of the source file are omitted.

The propositions `Function.Surjective (baseFixingCosetToAlgHom K Ω E)` and
`Function.Injective (baseFixingCosetToAlgHom K Ω E)` are the source
conclusions, unchanged.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection of each declaration
reports a definition whose type ends in `Prop` (`statement_returns_prop: true`),
with no level parameters and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. This development check is not independent
acceptance.

## Boundary and license

This file defines the propositions only. Their proofs, under the reserved
names `Langlands.NYLL.PortInternal.M165.d003` and
`Langlands.NYLL.PortInternal.M165.d004`, need a separate proof task once these
targets are in the Library.

The source proof of M165.003 extends a given `K`-embedding `f : E → Ω` to a
`K`-embedding `φ : Ω → Ω`. It uses Mathlib's
`IsSepClosed.surjective_domRestrict_of_isSeparable`, after deducing that
`Ω / E` is separable from `Ω / K`. Since `Ω / K` is normal, `φ` is bijective
(`Normal.toIsAlgebraic.algHom_bijective₂`), so it is an automorphism `σ`, and
the coset of `σ` maps to `f`. The source proof of M165.004 shows that equal
restrictions of coset representatives `σ`, `τ` imply that `σ⁻¹ τ` fixes `E`.
It uses the source lemma `mem_extensionSubgroup_iff`, which is not published.
Mathlib's `Subgroup.mem_subgroupOf` gives the same membership criterion,
because `extensionSubgroup` is an abbreviation for `Subgroup.subgroupOf`. A
proof may follow that route or another.

The Lean file keeps the original copyright and author header unchanged:
Copyright (c) 2026 Naganori Yamaguchi; Authors: Naganori Yamaguchi (assisted
by OpenAI Codex). It remains under Apache-2.0. The already-published
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are reused unchanged and
included through `repository_paths`. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Worker 85
adapted these units directly from the pinned original; no other project worker
supplied code.
