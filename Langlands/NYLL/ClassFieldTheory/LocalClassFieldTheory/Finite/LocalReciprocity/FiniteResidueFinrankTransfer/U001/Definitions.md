# The decomposition-field valuation ring when the decomposition group is everything (M252.001)

Let `Ω / F` be a Galois extension, possibly infinite. Let `A` be a valuation
subring of `Ω` and `C` a valuation subring of `F` with `A ∩ F = C`, that is,
`A.comap (algebraMap F Ω) = C`. Suppose that the decomposition group of `A`
over `F` is the whole Galois group: every `σ ∈ Gal(Ω / F)` maps `A` onto
itself. Then the decomposition field `Z` of `A`, the fixed field of the
decomposition group, is `F` itself. So the valuation ring `A ∩ Z` of the
decomposition field is `C`, transported along the identification `F ≅ Z`.
This module packages that identification as a ring equivalence:

- `Langlands.NYLL.LocalClassFieldTheory.valuationSubringEquivDecompositionFieldOfEqTop A C hC hA`
  is a ring equivalence `C ≃+* decompositionFieldValuationSubring F A`. It
  sends `x ∈ C` to `x` viewed as an element of the decomposition field. Its
  value in `Ω` is `algebraMap F Ω x`.

In Lean:

```lean
universe u v

noncomputable def valuationSubringEquivDecompositionFieldOfEqTop
    {F : Type u} {Omega : Type v} [Field F] [Field Omega] [Algebra F Omega]
    [IsGalois F Omega]
    (A : ValuationSubring Omega) (C : ValuationSubring F)
    (hC : A.comap (algebraMap F Omega) = C)
    (hA : decompositionGroup F A = ⊤) :
    C ≃+* decompositionFieldValuationSubring F A
```

The body is a tactic proof that builds the equivalence; the code block
shows only the type.

## The objects involved

All three objects named in the type are published abbreviations in the
namespace `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`:

- `decompositionGroup F A : Subgroup (Omega ≃ₐ[F] Omega)` is Mathlib's
  `A.decompositionSubgroup F`, the subgroup of automorphisms `σ` with
  `σ • A = A` (source unit M239.001, module
  `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions`);
- `decompositionField F A : IntermediateField F Omega` is the fixed field of
  `decompositionGroup F A` (M239.011, same module);
- `decompositionFieldValuationSubring F A : ValuationSubring (decompositionField F A)`
  is `A.comap (decompositionField F A).val`, the elements of the
  decomposition field that lie in `A` (M243.005, module
  `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Definitions`).

So the codomain is the subring `{z ∈ Z | (z : Ω) ∈ A}` of the decomposition
field `Z`, and the domain is the valuation ring `C` of `F`.

## How the body builds the equivalence

The body first proves `hZ : decompositionField F A = ⊥`. Since
`decompositionField F A` is by definition
`IntermediateField.fixedField (decompositionGroup F A)`, the hypothesis `hA`
rewrites it to `IntermediateField.fixedField ⊤`. Mathlib's
`InfiniteGalois.fixedField_fixingSubgroup ⊥` states that the fixed field of
the fixing subgroup of `⊥` is `⊥`. It uses `[IsGalois F Omega]`, and `simpa`
identifies the fixing subgroup of `⊥` with `⊤`. Galois theory is the only
place the body uses `[IsGalois F Omega]`.

It then sets `eFZ : F ≃ₐ[F] Z`. This is Mathlib's
`(IntermediateField.botEquiv F Omega).symm`, identifying `F` with the bottom
intermediate field, followed by `IntermediateField.equivOfEq hZ.symm`. For
`x : F`, the value of `eFZ x` in `Ω` is `algebraMap F Omega x`, by `rfl`.

The equivalence sends `x : C` to `⟨eFZ x, _⟩`; the inverse sends `z` to
`⟨eFZ.symm z, _⟩`. Both round trips and additivity and multiplicativity
follow from the same facts for `eFZ`, applied under `Subtype.ext`. The two
membership proofs are:

- `eFZ x` lies in `decompositionFieldValuationSubring F A`: its value in `Ω`
  is `algebraMap F Omega x`, which lies in `A` because
  `x ∈ C = A.comap (algebraMap F Omega)` by `hC`;
- `eFZ.symm z` lies in `C`: `algebraMap F Omega (eFZ.symm z)` equals the
  value of `z` in `Ω`, which lies in `A`. Hence `eFZ.symm z` lies in
  `A.comap (algebraMap F Omega)`, which is `C` by `hC`.

The hypotheses `hC` and `hA` are propositions. The underlying functions are
fixed: forward, `x ↦ eFZ x`, which has value `algebraMap F Omega x` in `Ω`;
backward, its inverse.

## Binders and universes

The binders are those of the source, unchanged: implicit `{F : Type u}` and
`{Omega : Type v}`, then `[Field F]`, `[Field Omega]`, `[Algebra F Omega]`,
`[IsGalois F Omega]`, then explicit `(A : ValuationSubring Omega)`,
`(C : ValuationSubring F)`, `hC` and `hA`. The declaration has the two
universe parameters `u` and `v` of the source line `universe u v`. The
ambient field is spelled `Omega`, as in the source.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFinrankTransfer.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFinrankTransfer.lean),
SHA-256 `2a282f270893fba7c9c47573e1f5dad6ac27f8310981b0bb61f251fbe38b46ed`.
The relevant lines are:

- the namespace, opens and universes, lines 22–34: `namespace
  LocalClassFieldTheory`, `open CyclicCohomology RamificationTheory
  ClassFormation`, `open LocalFieldTheory ValuationTheory`, `noncomputable
  section`, `open scoped ValuativeRel`, `open
  HilbertRamification.ValuationSubring`, `universe u v`;
- M252.001: docstring at lines 36–38, definition and body at lines 39–89.

The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution is also registered
as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Library's `notes/errata/` has no NYLL entry.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.valuationSubringEquivDecompositionFieldOfEqTop` (M252.001) | `Langlands.NYLL.LocalClassFieldTheory.valuationSubringEquivDecompositionFieldOfEqTop` (this module) |
| `RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` (M239.001, used) | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` (published) |
| `RamificationTheory.HilbertRamification.ValuationSubring.decompositionField` (M239.011, used) | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionField` (published) |
| `RamificationTheory.HilbertRamification.ValuationSubring.decompositionFieldValuationSubring` (M243.005, used) | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFieldValuationSubring` (published) |

Row M252.001 of the published partition
[`notes/reuse/nyll-public-port/m241-m258.md`](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md)
reserves the adapted name and the module stem
`Langlands/NYLL/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFinrankTransfer`.
No declaration named `valuationSubringEquivDecompositionFieldOfEqTop` exists
in the current Library or Mathlib.

## Imports and modification record

The only direct import is
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Definitions`.
It defines `decompositionFieldValuationSubring` and imports the module
defining `decompositionGroup` and `decompositionField`, together with
`Mathlib.FieldTheory.Galois.Infinite`, which supplies
`InfiniteGalois.fixedField_fixingSubgroup` and `IsGalois`.
`IntermediateField.botEquiv` and `IntermediateField.equivOfEq` reach the
module through these imports. The import replaces the source's four imports
(`FiniteSubgroupResidueDegree`, `FiniteResidueValuationComparison`,
`ResidueExtension` and `Valuation.UniqueRing`), which serve the other
declarations of the source file. Every transitive import lies in the
approved Mathlib environment or the published Library.

Worker 85 extracted this one source definition on 14 November 2026. The Lean
header records the change. The changes are:

- the namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`;
- the imports are replaced as described above;
- of the source's opens, only `open RamificationTheory` and
  `open HilbertRamification.ValuationSubring` are kept. Inside the new
  namespace they resolve to `Langlands.NYLL.RamificationTheory` and
  `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
  which supply `decompositionGroup`, `decompositionField` and
  `decompositionFieldValuationSubring`. The opened namespaces
  `CyclicCohomology`, `ClassFormation`, `LocalFieldTheory`,
  `ValuationTheory` and the scoped `ValuativeRel` notation provide nothing
  this definition uses, and are omitted.

The `noncomputable section`, the universe line, the docstring, the binders,
the type and the body (lines 39–89, compared line by line) are unchanged.
Every other source declaration is omitted: the residue-field equivalence
M252.002, its `algebraMap` lemma M252.003 and the residue-degree comparison
M252.004. No theorem, instance, notation or alias is introduced.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection of
`valuationSubringEquivDecompositionFieldOfEqTop` reports a definition with
level parameters `u` and `v` and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. This development check is not
independent acceptance.

## Use downstream

The source passes this equivalence to residue fields with Mathlib's
`IsLocalRing.ResidueField.mapEquiv` and composes the result with
`decompositionFieldResidueEquiv` (M243.018, not yet in the Library). This
gives `residueFieldEquivDecompositionResidueOfEqTop` (M252.002, source
lines 90–101), which identifies the literal residue field of `C` with the
intrinsic residue field `decompositionResidueField F A` of the
residue-action exact sequence. It is used to compare residue degrees
(M252.004).

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
