# Literal and intrinsic residue fields when the decomposition group is everything (M252.002)

Let `Ω / F` be a Galois extension, possibly infinite. Let `A` be a valuation
subring of `Ω` and `C` a valuation subring of `F` with `A ∩ F = C`, that is,
`A.comap (algebraMap F Ω) = C`, and suppose that the decomposition group of
`A` over `F` is the whole Galois group. The published M252.001 equivalence
identifies `C` with the valuation ring of the decomposition field. This
module passes that identification to residue fields and composes it with the
published comparison M243.018, which identifies the residue field of the
decomposition-field valuation ring with the intrinsic residue field of the
residue-action exact sequence:

- `Langlands.NYLL.LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop A C hC hA`
  is a ring equivalence from the literal residue field of `C` to
  `decompositionResidueField F A`.

In Lean:

```lean
universe u v

noncomputable def residueFieldEquivDecompositionResidueOfEqTop
    {F : Type u} {Omega : Type v} [Field F] [Field Omega] [Algebra F Omega]
    [IsGalois F Omega]
    (A : ValuationSubring Omega) (C : ValuationSubring F)
    (hC : A.comap (algebraMap F Omega) = C)
    (hA : decompositionGroup F A = ⊤) :
    IsLocalRing.ResidueField C ≃+* decompositionResidueField F A :=
  (IsLocalRing.ResidueField.mapEquiv
      (valuationSubringEquivDecompositionFieldOfEqTop A C hC hA)).trans
    (decompositionFieldResidueEquiv (K := F) A)
```

## The objects involved

- `valuationSubringEquivDecompositionFieldOfEqTop A C hC hA :
  C ≃+* decompositionFieldValuationSubring F A` is the published M252.001
  equivalence (module
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFinrankTransfer.U001.Definitions`).
  It sends `x ∈ C` to `x` viewed in the decomposition field; its value in `Ω`
  is `algebraMap F Ω x`.
- `IsLocalRing.ResidueField.mapEquiv` is Mathlib's: a ring equivalence of
  local rings induces a ring equivalence of their residue fields.
- `decompositionFieldResidueEquiv (K := F) A :
  IsLocalRing.ResidueField (decompositionFieldValuationSubring F A) ≃+*
  decompositionResidueField F A` is the published M243.018 comparison, in
  namespace `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`
  (module
  `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueComparison`).
- `decompositionResidueField F A` (M243.003, same namespace, module
  `...ResidueExactSequence.Definitions`) is the abbreviation for the quotient
  `decompositionFixedSubring F A ⧸ decompositionFixedMaximalIdeal F A` of the
  elements of `A` fixed by the decomposition group by the contraction of the
  maximal ideal of `A`.
- `decompositionGroup F A` (M239.001) is Mathlib's `A.decompositionSubgroup F`.

So, on residues, the equivalence sends the residue class of `x ∈ C` first to
the residue class of `x` in the decomposition-field valuation ring, then to
the class of `x` in the intrinsic quotient.

## Binders and universes

The binders are those of the source, unchanged: implicit `{F : Type u}` and
`{Omega : Type v}`, then `[Field F]`, `[Field Omega]`, `[Algebra F Omega]`,
`[IsGalois F Omega]`, then explicit `(A : ValuationSubring Omega)`,
`(C : ValuationSubring F)`, `hC` and `hA`. The declaration has the two
universe parameters `u` and `v` of the source line `universe u v`. The
ambient field is spelled `Omega`, as in the source. The hypotheses `hC` and
`hA` are propositions and are used only by the M252.001 equivalence.

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
- M252.002: docstring at lines 90–91, definition and body at lines 92–101.

The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution is also registered
as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Library's `notes/errata/` has no NYLL entry.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop` (M252.002) | `Langlands.NYLL.LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop` (this module) |
| `LocalClassFieldTheory.valuationSubringEquivDecompositionFieldOfEqTop` (M252.001, used) | `Langlands.NYLL.LocalClassFieldTheory.valuationSubringEquivDecompositionFieldOfEqTop` (published) |
| `RamificationTheory.HilbertRamification.ValuationSubring.decompositionFieldResidueEquiv` (M243.018, used) | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFieldResidueEquiv` (published) |
| `RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField` (M243.003, used) | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField` (published) |
| `RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` (M239.001, used) | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` (published) |

Row M252.002 of the published partition
[`notes/reuse/nyll-public-port/m241-m258.md`](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md)
reserves the adapted name and the module stem
`Langlands/NYLL/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFinrankTransfer`.
No declaration named `residueFieldEquivDecompositionResidueOfEqTop` exists in
the current Library or Mathlib.

## Imports and modification record

The direct imports are
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFinrankTransfer.U001.Definitions`
(M252.001, which also brings `decompositionGroup`, `decompositionResidueField`
and `decompositionFieldValuationSubring`) and
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueComparison`
(M243.018). `IsLocalRing.ResidueField.mapEquiv` and the `IsLocalRing`
instances it needs reach the module through these imports. The imports
replace the source's four imports (`FiniteSubgroupResidueDegree`,
`FiniteResidueValuationComparison`, `ResidueExtension` and
`Valuation.UniqueRing`), which serve the other declarations of the source
file. Every transitive import lies in the approved Mathlib environment or the
published Library.

Worker 85 extracted this one source definition on 14 November 2026. The Lean
header records the change. The changes are:

- the namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`;
- the imports are replaced as described above;
- of the source's opens, only `open RamificationTheory` and
  `open HilbertRamification.ValuationSubring` are kept. Inside the new
  namespace they resolve to `Langlands.NYLL.RamificationTheory` and
  `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
  which supply `decompositionGroup`, `decompositionResidueField`,
  `decompositionFieldValuationSubring` and `decompositionFieldResidueEquiv`.
  The opened namespaces `CyclicCohomology`, `ClassFormation`,
  `LocalFieldTheory`, `ValuationTheory` and the scoped `ValuativeRel`
  notation provide nothing this definition uses, and are omitted.

The `noncomputable section`, the universe line, the docstring, the binders,
the type and the body (lines 90–101, compared line by line) are unchanged.
Every other source declaration is omitted: M252.001 is published separately,
and the `algebraMap` lemma M252.003 and the residue-degree comparison M252.004
are later units. No theorem, instance, notation or alias is introduced.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection of
`residueFieldEquivDecompositionResidueOfEqTop` reports a definition with
level parameters `u` and `v` and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. This development check is not
independent acceptance.

## Use downstream

The source lemma `residueFieldEquivDecompositionResidueOfEqTop_algebraMap`
(M252.003, lines 103–120) states that this equivalence followed by the
algebra map from `decompositionResidueField F A` to the selected residue field
of `A` is reduction of `algebraMap F Ω x` modulo the maximal ideal of `A`,
by `rfl`. The residue-degree comparison M252.004 uses the equivalence to
compare the literal residue degree of a finite fixed field with the intrinsic
one.

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
