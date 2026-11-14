# Cosets of the base fixing subgroup as embeddings: the equivalence (M165.005)

Let `Ω / K` be a Galois extension with `Ω` separably closed, and let `E` be
an intermediate field that is finite-dimensional and separable over `K`.
Restriction to `E` sends a left coset `σ · Gal(Ω / E)` of `Gal(Ω / K)` to
the `K`-embedding `σ|_E : E → Ω`. This map is a bijection, and this module
packages it as an equivalence:

- `Langlands.NYLL.LocalClassFieldTheory.baseFixingCosetEquivAlgHom K Ω E`
  is the equivalence between the left cosets of `Gal(Ω / E)` in
  `Gal(Ω / K)` and the `K`-embeddings `E →ₐ[K] Ω`. Its forward map is the
  published restriction map `baseFixingCosetToAlgHom K Ω E`.

In Lean:

```lean
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]

variable (E : IntermediateField K Ω)

def baseFixingCosetEquivAlgHom
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) ≃
      (E →ₐ[K] Ω) :=
  Equiv.ofBijective (baseFixingCosetToAlgHom K Ω E)
    ⟨Langlands.NYLL.PortInternal.M165.d004 K Ω E,
      Langlands.NYLL.PortInternal.M165.d003 K Ω E⟩
```

## The objects involved

The domain is the quotient used by the published restriction map
`Langlands.NYLL.LocalClassFieldTheory.baseFixingCosetToAlgHom` (source unit
M165.001, module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.Initial.Definitions`).
It is the quotient of `(closedFixingSubgroup K Ω ⊥).toSubgroup`, which is
all of `Gal(Ω / K)` presented as a subgroup, by `extensionSubgroup` of the
closed subgroup `closedFixingSubgroup K Ω E`, which is `Gal(Ω / E)` viewed
inside it. Its elements are left cosets. The paired Markdown of the
restriction map's module describes these published objects in detail. The
codomain `E →ₐ[K] Ω` is the type of `K`-algebra homomorphisms from `E` to
`Ω`.

The body is Mathlib's `Equiv.ofBijective f h`. Given a function `f` and a
proof `h : Function.Bijective f`, it is the equivalence whose forward map is
`f` and whose inverse is chosen from `h` by `Function.surjInv`. Here `f` is
`baseFixingCosetToAlgHom K Ω E`. The proof `h` is the pair of two published
theorems:

- `Langlands.NYLL.PortInternal.M165.d004 K Ω E`, of type
  `Langlands.NYLL.PortInternal.M165.d004Statement K Ω E`, which unfolds to
  `Function.Injective (baseFixingCosetToAlgHom K Ω E)` (source unit
  M165.004, module `...SeparableFixedFieldNorm.Initial.U004.Proofs`);
- `Langlands.NYLL.PortInternal.M165.d003 K Ω E`, of type
  `Langlands.NYLL.PortInternal.M165.d003Statement K Ω E`, which unfolds to
  `Function.Surjective (baseFixingCosetToAlgHom K Ω E)` (source unit
  M165.003, module `...SeparableFixedFieldNorm.Initial.U003.Proofs`).

`Function.Bijective f` is by definition `Function.Injective f ∧
Function.Surjective f`, so the anonymous pair is a proof of bijectivity.
These two proofs are propositions, so they fix no data. The forward map of
the equivalence is exactly `baseFixingCosetToAlgHom K Ω E`.

## Section variables and binders

The section variables are those of the source, unchanged:
`(K Ω : Type)`, then `[Field K]`, `[Field Ω]`, `[Algebra K Ω]`,
`[IsGalois K Ω]`, `[IsSepClosed Ω]`, then `(E : IntermediateField K Ω)`.
The definition adds the source binders `[FiniteDimensional K E]` and
`[Algebra.IsSeparable K E]`. The fields are in `Type` (universe 0), as in
the source; the declaration has no universe parameter.

The body uses `[IsSepClosed Ω]`, `[FiniteDimensional K E]` and
`[Algebra.IsSeparable K E]`, because the surjectivity theorem
`Langlands.NYLL.PortInternal.M165.d003` takes these three instances. So
`baseFixingCosetEquivAlgHom` takes all the section variables above and the
two extra binders, as the source definition does.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean),
SHA-256 `477273f35f3c5945fe5ccb5cb38e4527f2656e8f3f2ef85451aef32c639e4106`.
The relevant lines are:

- the namespace and opens, lines 23–34: `namespace LocalClassFieldTheory`,
  `open RamificationTheory KummerTheory`, `open LocalFieldTheory`,
  `open ClassFormation CyclicCohomology`, `noncomputable section`,
  `open scoped BigOperators`;
- the section variables, lines 36–37 and 41 (the latter inside
  `section CosetsAndEmbeddings`, line 39);
- M165.005: docstring at lines 141–142, definition at lines 143–152.

The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution is also registered
as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Library's `notes/errata/` has no NYLL entry.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.baseFixingCosetEquivAlgHom` (M165.005) | `Langlands.NYLL.LocalClassFieldTheory.baseFixingCosetEquivAlgHom` (this module) |
| `LocalClassFieldTheory.baseFixingCosetToAlgHom` (M165.001, used) | `Langlands.NYLL.LocalClassFieldTheory.baseFixingCosetToAlgHom` (published) |
| private `LocalClassFieldTheory.baseFixingCosetToAlgHom_surjective` (M165.003, used) | `Langlands.NYLL.PortInternal.M165.d003` (published) |
| private `LocalClassFieldTheory.baseFixingCosetToAlgHom_injective` (M165.004, used) | `Langlands.NYLL.PortInternal.M165.d004` (published) |
| `RamificationTheory.closedFixingSubgroup` (M087.001, used) | `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` (published) |
| `CyclicCohomology.extensionSubgroup` (M004.002, used) | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (published) |
| `LocalClassFieldTheory.fixingSubgroupLeBase` (M089.002, used) | `Langlands.NYLL.LocalClassFieldTheory.fixingSubgroupLeBase` (published) |

Row M165.005 of the published partition
[`notes/reuse/nyll-public-port/m145-m168.md`](../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md)
reserves the adapted name. The same partition reserves the names
`Langlands.NYLL.PortInternal.M165.d003` and `d004` for the two private
source theorems. No declaration named `baseFixingCosetEquivAlgHom` exists in
the current Library or Mathlib.

## Imports and modification record

The direct imports are:

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.Initial.U003.Proofs`,
  proving `Langlands.NYLL.PortInternal.M165.d003`;
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.Initial.U004.Proofs`,
  proving `Langlands.NYLL.PortInternal.M165.d004`.

Through them come `baseFixingCosetToAlgHom`, `closedFixingSubgroup`,
`extensionSubgroup`, `fixingSubgroupLeBase` and Mathlib's
`Equiv.ofBijective`, `IsSepClosed` and `Algebra.IsSeparable`. These imports
replace the source's two NYLL imports (`SeparableNormProduct` and
`SeparableUnitsNorm`) and its Mathlib import
`Mathlib.FieldTheory.PrimitiveElement`, which reaches this module through
the restriction map's module. Every transitive import lies in the approved
Mathlib environment or the published Library.

Worker 85 extracted this one source definition on 14 November 2026. The Lean
header records the change. The changes are:

- the namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`;
- the imports are replaced as described above;
- in the body, the private source theorems
  `baseFixingCosetToAlgHom_injective K Ω E` and
  `baseFixingCosetToAlgHom_surjective K Ω E` are replaced by their published
  adaptations `Langlands.NYLL.PortInternal.M165.d004 K Ω E` and
  `Langlands.NYLL.PortInternal.M165.d003 K Ω E`. Their statements are the
  same propositions, and they take the same explicit arguments `K Ω E`;
- of the source's opens, only `RamificationTheory` and `CyclicCohomology` are
  kept, as one `open` line. Inside the new namespace they resolve to
  `Langlands.NYLL.RamificationTheory` and `Langlands.NYLL.CyclicCohomology`,
  which supply `closedFixingSubgroup` and `extensionSubgroup`. The other
  opened namespaces (`KummerTheory`, `LocalFieldTheory`, `ClassFormation`,
  scoped `BigOperators`) provide nothing this definition uses.

The section variables, the section `CosetsAndEmbeddings`, the
`noncomputable section`, the docstring, the type and the `Equiv.ofBijective`
body are unchanged. Every other source declaration is omitted: the
restriction map M165.001 and its `@[simp]` lemma M165.002, the private
theorems M165.003 and M165.004, the instance M165.006 and the norm
comparison results M165.007–M165.010. No theorem, instance, notation or
alias is introduced.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection of
`baseFixingCosetEquivAlgHom` reports a definition with no level parameters and
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
This development check is not independent acceptance.

## Use downstream

The source uses this equivalence to show that the coset space is finite
(the instance M165.006, from the finiteness of `E →ₐ[K] Ω`). It then
compares the abstract class-formation coset norm with the ordinary field
norm for finite separable intermediate fields that need not be normal
(M165.008–M165.010).

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex); Apache-2.0. The original
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain in `licenses/NYLL/`. Worker 85 adapted this unit directly from the
pinned original; no other project worker supplied code.
