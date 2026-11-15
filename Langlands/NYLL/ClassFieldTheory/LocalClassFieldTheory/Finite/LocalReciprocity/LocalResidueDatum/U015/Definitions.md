# A finite enumeration of the local decomposition residue field (M249.015)

Let `K` be a nonarchimedean local field (a field with `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField` instances). Finite local
reciprocity fixes a valuation ring `A = localSeparableValuationSubring K` of
the separable closure `SeparableClosure K`. The base residue field
`κ = decompositionResidueField K A` of the residue-action exact sequence is
isomorphic to the residue field of `K`, so it is finite.

This module defines the global instance
`Langlands.NYLL.LocalClassFieldTheory.localDecompositionResidueFintype K`
(source unit M249.015): a `Fintype` structure on `κ`, namely Mathlib's
`Fintype.ofFinite`, which enumerates a finite type by choice.

In Lean, with `variable (K : Type) [Field K] [ValuativeRel K]
[TopologicalSpace K] [IsNonarchimedeanLocalField K]`:

```lean
noncomputable instance Langlands.NYLL.LocalClassFieldTheory.localDecompositionResidueFintype :
    Fintype (decompositionResidueField K
      (localSeparableValuationSubring K)) :=
  haveI : Finite (decompositionResidueField K
      (localSeparableValuationSubring K)) := by
    have : Finite (localCompleteDVF K).residueField := by
      change Finite 𝓀[K]
      infer_instance
    exact Finite.of_equiv (localCompleteDVF K).residueField
      (localBaseResidueEquivDecompositionResidue K).toEquiv
  Fintype.ofFinite _
```

The instance is the data `Fintype.ofFinite κ`. Its `Finite κ` argument is a
proposition, so the way it is proved does not change the instance.

## The objects involved

- `localSeparableValuationSubring K : ValuationSubring (SeparableClosure K)`
  is the chosen valuation ring `A` (M249.006, module
  `...LocalReciprocity.LocalResidueDatum.U006.Definitions`).
- `decompositionResidueField K A` (M243.003, namespace
  `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`)
  is the base residue field `κ` of the residue-action exact sequence: the
  quotient of the subring of `A` fixed by the decomposition group by the
  contraction of the maximal ideal of `A`.
- `localCompleteDVF K` is the canonical complete discrete valuation of `K`
  (namespace `Langlands.NYLL.LocalFieldTheory`, module
  `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.Canonical`).
  `(localCompleteDVF K).residueField` is the residue field of its valuation
  ring. It is definitionally Mathlib's residue field `𝓀[K]` of the
  `ValuativeRel` integers of `K` (the `change` below succeeds).
- `localBaseResidueEquivDecompositionResidue K :
  (localCompleteDVF K).residueField ≃+* κ` is the published ring equivalence
  M249.012 (module `...LocalReciprocity.LocalResidueDatum.U011.Definitions`).
- `Fintype.ofFinite α : Fintype α` is Mathlib's noncomputable `Fintype`
  structure on a type with a `Finite α` instance.

## Why the finiteness proof is in this body

In the source, `Fintype.ofFinite _` finds its `Finite κ` argument from the
source instance `localDecompositionResidueFinite` (M249.014, lines 252–260).
The port publishes its type as the closed target
`localDecompositionResidueFiniteStatement` (module
`...LocalResidueDatum.U014.Statements`). Its proof is not yet in the Library
(proof Task 6979). So the body proves the finiteness fact by a local
`haveI`, with the source proof of M249.014, and then applies
`Fintype.ofFinite _` as in the source. When the M249.014 proof is
published, the two `Finite` proofs are equal by proof irrelevance, so the
instance does not change. A development probe (not part of this candidate)
checked by `rfl` that, for every proof `h` of the M249.014 target,
`localDecompositionResidueFintype K = @Fintype.ofFinite _ (h K)`.

The finiteness proof has two steps:

1. `(localCompleteDVF K).residueField` is finite: `change` turns it into
   `𝓀[K]`, and Mathlib's instance `Finite 𝓀[K]` for nonarchimedean local
   fields (`Mathlib.NumberTheory.LocalField.Basic`) applies.
2. `Finite.of_equiv` transfers finiteness along the underlying equivalence
   of `localBaseResidueEquivDecompositionResidue K`.

## Binders and universes

The instance takes the explicit field `(K : Type)` and the instance binders
`[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]` of the source section variables. `K` lives in
`Type`, as in the source. The declaration has no universe parameters. It is a
global instance, as in the source; instance search finds it for
`Fintype (decompositionResidueField K (localSeparableValuationSubring K))`.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean),
SHA-256 `be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`.
The relevant lines are:

- the namespace, opens and section variables, lines 31–46:
  `namespace LocalClassFieldTheory`, `open ClassFormation`,
  `open ValuationTheory RamificationTheory LocalFieldTheory`,
  `noncomputable section`, `open scoped Pointwise ValuativeRel`,
  `open HilbertRamification.ValuationSubring`,
  `open Field.absoluteGaloisGroup`, and the `variable` line for `K`;
- M249.014, instance `localDecompositionResidueFinite`: docstring at line
  252, declaration at lines 253–255, proof at lines 256–260 (proof inlined);
- M249.015: docstring at line 262, instance at lines 263–266.

The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution is also registered
as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Library's `notes/errata/` has no NYLL entry.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.localDecompositionResidueFintype` (M249.015) | `Langlands.NYLL.LocalClassFieldTheory.localDecompositionResidueFintype` (this module) |
| `LocalClassFieldTheory.localDecompositionResidueFinite` (M249.014, used) | local fact in this body; closed target `localDecompositionResidueFiniteStatement` published |
| `LocalClassFieldTheory.localBaseResidueEquivDecompositionResidue` (M249.012, used) | `Langlands.NYLL.LocalClassFieldTheory.localBaseResidueEquivDecompositionResidue` (published) |
| `LocalFieldTheory.localCompleteDVF` (used) | `Langlands.NYLL.LocalFieldTheory.localCompleteDVF` (published) |
| `LocalClassFieldTheory.localSeparableValuationSubring` (M249.006, used) | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring` (published) |
| `RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField` (M243.003, used) | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField` (published) |

Row M249.015 of the published partition
[`notes/reuse/nyll-public-port/m241-m258.md`](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md)
reserves the adapted name and the module stem
`Langlands/NYLL/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum`.
The name does not exist in the current Library or Mathlib. The Library has
no other `Fintype` or `Finite` instance on this residue field: the only
Library occurrence of `localDecompositionResidueFinite` is the docstring of
the M249.014 target.

## Imports and modification record

The only direct import is the published module
`...LocalReciprocity.LocalResidueDatum.U011.Definitions` (M249.012). It
imports the definitions of `localSeparableValuationSubring`,
`decompositionResidueField` and `localCompleteDVF` with its projections. It replaces the source's four imports
(`ResidueActionIndex`, `FiniteIntegralClosure`,
`FiniteExtensionCorrespondence` and `FiniteExtensionCompleteDVF`), which
serve the other declarations of the source file. Every transitive import lies
in the approved Mathlib environment or the published Library.

Worker 85 extracted this source instance on 15 November 2026. The Lean header
records the change. The changes are:

- the instance is in the namespace `Langlands.NYLL.LocalClassFieldTheory`.
  Its docstring and type are the source text;
- the source body `Fintype.ofFinite _` is preceded by a local `haveI` proving
  `Finite κ` with the source proof of M249.014 (lines 256–260, compared line
  by line), as explained above;
- the imports are replaced as described above;
- the source opens are replaced by `open scoped ValuativeRel` (for the
  notation `𝓀[K]`) and the fully qualified opens of
  `Langlands.NYLL.LocalFieldTheory` (for `localCompleteDVF`) and
  `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`.
  The opens of `ClassFormation`, `ValuationTheory`,
  `Field.absoluteGaloisGroup` and the scoped `Pointwise` notation provide
  nothing this instance uses, and are omitted.

The source's two local instances (M249.001, M249.002) are not needed and are
not activated. Every other source declaration is omitted; in particular the
`Finite` instance M249.014 is not declared here (it is the proof unit of Task
6979). No theorem, notation or alias is introduced; the `haveI` is local to
the body.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection reports the
declaration as a definition without level parameters, depending only on the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. The
development probe also checked that instance search finds the instance. This
development check is not independent acceptance.

## Use downstream

In the source, instance search uses this instance for the `[Fintype k]`
binder of the intrinsic finite-field degree map `residueAbsoluteDegreeIn`,
applied with `k = κ` in the local degree map `localResidueDegree` (M249.022,
lines 400–415).

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
