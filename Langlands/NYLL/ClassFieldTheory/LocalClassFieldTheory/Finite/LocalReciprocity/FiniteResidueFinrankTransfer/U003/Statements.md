# Naturality of the literal-to-intrinsic residue equivalence (M252.003, proposition target)

Let `Ω / F` be a Galois extension, possibly infinite. Let `A` be a valuation
subring of `Ω` and `C` a valuation subring of `F` with `A ∩ F = C`, that is,
`hC : A.comap (algebraMap F Ω) = C`, and suppose that the decomposition group
of `A` over `F` is the whole Galois group (`hA`). The published M252.002
equivalence

```lean
residueFieldEquivDecompositionResidueOfEqTop A C hC hA :
  IsLocalRing.ResidueField C ≃+* decompositionResidueField F A
```

identifies the literal residue field of `C` with the intrinsic residue field
`κ_F = decompositionResidueField F A` of the residue-action exact sequence.
The intrinsic field maps to the residue field `λ = selectedResidueField A` of
`A`. This module states that the two ways from `C` to `λ` agree: for `x ∈ C`,
reducing `x` in `C`, applying the equivalence and then the structure map
`κ_F → λ` gives the residue class in `λ` of `x` viewed as an element of `A`.

```lean
universe u v

def residueFieldEquivDecompositionResidueOfEqTop_algebraMapStatement
    {F : Type u} {Omega : Type v} [Field F] [Field Omega] [Algebra F Omega]
    [IsGalois F Omega]
    (A : ValuationSubring Omega) (C : ValuationSubring F)
    (hC : A.comap (algebraMap F Omega) = C)
    (hA : decompositionGroup F A = ⊤) (x : C) : Prop :=
    algebraMap (decompositionResidueField F A) (selectedResidueField A)
        (residueFieldEquivDecompositionResidueOfEqTop A C hC hA
          (IsLocalRing.residue C x)) =
      IsLocalRing.residue A
        (⟨algebraMap F Omega (x : F), by
          have hx : (x : F) ∈ A.comap (algebraMap F Omega) := by
            rw [hC]
            exact x.property
          exact hx⟩ : A)
```

The declaration is
`Langlands.NYLL.LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop_algebraMapStatement`,
a `def` of type `Prop` with the source theorem's binders as parameters. It
asserts nothing by itself. A proof is a separate unit (see below).

The element on the right is `algebraMap F Ω x` with the membership proof
written in the source: `x ∈ C = A.comap (algebraMap F Ω)` (rewriting with
`hC`), so `algebraMap F Ω x ∈ A`. This proof term is part of the source type
and is kept unchanged. By proof irrelevance any other membership proof gives
the same element of `A`.

## The objects involved

- `residueFieldEquivDecompositionResidueOfEqTop` (M252.002), module
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFinrankTransfer.U002.Definitions`,
  in namespace `Langlands.NYLL.LocalClassFieldTheory`: Mathlib's
  `IsLocalRing.ResidueField.mapEquiv` of the M252.001 equivalence
  `C ≃+* decompositionFieldValuationSubring F A`, followed by the published
  comparison `decompositionFieldResidueEquiv (K := F) A` (M243.018).
- `decompositionResidueField F A` (M243.003) and `selectedResidueField A`
  (M243.004, Mathlib's `IsLocalRing.ResidueField A`), in namespace
  `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
  module
  `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Definitions`.
- `decompositionGroup F A` (M239.001), Mathlib's `A.decompositionSubgroup F`.
- The structure map `algebraMap (decompositionResidueField F A)
  (selectedResidueField A)` is the published instance
  `selectedResidueField.instAlgebra F A` (M243.021) in
  `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueFields`:
  the class of `a` in the quotient of the decomposition-fixed subring of `A`
  goes to the residue class of `a` in `λ`. The field structure on `κ_F` is
  `decompositionResidueField.instField F A` (M243.020), same module.
- `IsLocalRing.residue` is Mathlib's residue map of a local ring.

## Source and declaration map

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFinrankTransfer.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFinrankTransfer.lean),
SHA-256 `2a282f270893fba7c9c47573e1f5dad6ac27f8310981b0bb61f251fbe38b46ed`:

- namespace, opens and universes, lines 22–34 (`namespace
  LocalClassFieldTheory`, `open CyclicCohomology RamificationTheory
  ClassFormation`, `open LocalFieldTheory ValuationTheory`,
  `noncomputable section`, `open scoped ValuativeRel`, `open
  HilbertRamification.ValuationSubring`, `universe u v`);
- M252.003: docstring at lines 103–104, `theorem
  residueFieldEquivDecompositionResidueOfEqTop_algebraMap` and its type at
  lines 105–119. Its proof, `rfl` at line 120, is not part of this module.

The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution is also registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
Library's `notes/errata/` has no NYLL entry.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop_algebraMap` (M252.003; type) | `Langlands.NYLL.LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop_algebraMapStatement` (this module) |
| `LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop` (M252.002, used) | `Langlands.NYLL.LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop` (published) |
| `RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField` / `selectedResidueField` (M243.003/.004, used) | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField` / `selectedResidueField` (published) |
| `RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField`, `selectedResidueField.instAlgebra` (M243.020/.021, instances used) | same names under `Langlands.NYLL.` (published) |

Row M252.003 of the published partition
[`notes/reuse/nyll-public-port/m241-m258.md`](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md)
reserves the adapted name; the target is that name with the suffix
`Statement`. No declaration with this name exists in the current Library or
Mathlib.

## Adaptation

The binders `{F : Type u} {Omega : Type v} [Field F] [Field Omega]
[Algebra F Omega] [IsGalois F Omega] (A) (C) (hC) (hA) (x)` are the source
theorem's own binders, in the same order and with the same binder kinds; the
target has the two universe parameters `u v` of the source. The body is the
source type unchanged, and the source docstring is kept.

The changes are:

- the source theorem becomes a proposition-valued `def` named with the suffix
  `Statement`;
- the namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`;
- of the source opens only `open RamificationTheory` and
  `open HilbertRamification.ValuationSubring` are kept. Inside the new
  namespace they resolve to `Langlands.NYLL.RamificationTheory` and
  `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`.
  `CyclicCohomology`, `ClassFormation`, `LocalFieldTheory`, `ValuationTheory`
  and the scoped `ValuativeRel` notation provide nothing the type uses;
- the source imports are replaced by the two published modules
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFinrankTransfer.U002.Definitions`
  (M252.002, and through its imports M243.003/.004 and M239.001) and
  `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueFields`
  (the instances M243.020/.021). Every transitive import lies in the approved
  Mathlib environment or the published Library;
- the proof and all other source declarations are omitted.

## Development evidence and the proof unit

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). In a private probe (not part of
this candidate) the source proof `rfl` proves this exact target for arbitrary
binders. The proof of this target is a separate `lean.proof@1` unit. This is
development evidence, not independent acceptance.

## Use downstream

In the source, the proof of `localResidueDatum_residueDegree_eq_residueFinrank`
(M252.004) in the same file rewrites with this naturality square (line 221) to
transport the residue degree between the literal residue field of the spectral
valuation on a finite fixed field and the intrinsic residue field. Proofs in
`FixedFieldLocalData.lean` (lines 477, 488 and 882) rewrite with it in the
same way.

## Attribution

The original copyright and author header is retained verbatim at the top of
the Lean file: copyright 2026 Naganori Yamaguchi, all rights reserved; authors
Naganori Yamaguchi (assisted by OpenAI Codex); Apache-2.0. A modification
notice follows it. The retained files are
[`licenses/NYLL/LICENSE`](../../../../../../../../licenses/NYLL/LICENSE),
SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and [`licenses/NYLL/NOTICE`](../../../../../../../../licenses/NYLL/NOTICE),
SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 85 adapted this unit directly from the pinned original; no other project
worker supplied code.
