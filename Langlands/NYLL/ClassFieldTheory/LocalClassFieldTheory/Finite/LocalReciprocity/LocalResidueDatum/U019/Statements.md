# Continuity of the local residue action (M249.019, proposition target)

Let `K` be a nonarchimedean local field, `Ω = SeparableClosure K`, and
`A = localSeparableValuationSubring K` the valuation ring on `Ω` chosen for
finite local reciprocity. Every element of `Gal(Ω / K)` maps `A` to itself
(the published theorem `localSeparableDecompositionGroup_eq_top`, M249.010),
so the residue action of the decomposition group is an action of the whole
Galois group on the residue field `λ = selectedResidueField A` of `A`, over the
base residue field `κ = decompositionResidueField K A`. This is the published
homomorphism

```lean
residueAlgActionOfEqTop K A (localSeparableDecompositionGroup_eq_top K) :
  Gal(Ω / K) →* (λ ≃ₐ[κ] λ)
```

(M244.003). This module states that this homomorphism is continuous when both
automorphism groups carry their Krull topologies:

```lean
def d019Statement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    Continuous
      (residueAlgActionOfEqTop K
        (localSeparableValuationSubring K)
        (localSeparableDecompositionGroup_eq_top K))
```

The declaration is `Langlands.NYLL.PortInternal.M249.d019Statement`. It is a
`def` of type `Prop` and asserts nothing by itself. A proof is a separate unit
(see below).

## Meaning

`Continuous` refers to Mathlib's `krullTopology` instances on
`Gal(Ω / K) = Ω ≃ₐ[K] Ω` and on `λ ≃ₐ[κ] λ`. A basic neighbourhood of the
identity in the Krull topology is the subgroup fixing a finite-dimensional
intermediate field. So the statement says: for every finite extension `E` of
`κ` inside `λ`, there is a finite extension `F` of `K` inside `Ω` such that
every `σ ∈ Gal(Ω / F)` acts trivially on `E`. The function is coerced from
the monoid homomorphism `residueAlgActionOfEqTop …`; `σ` acts on `λ` by
reducing modulo the maximal ideal of `A`: the class of `a ∈ A` goes to the
class of `σ a`.

## Source and declaration map

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean),
SHA-256 `be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`:

- namespace, opens and section variables, lines 31–46 (`namespace
  LocalClassFieldTheory`, `open ClassFormation`, `open ValuationTheory
  RamificationTheory LocalFieldTheory`, `noncomputable section`,
  `open scoped Pointwise ValuativeRel`, `open
  HilbertRamification.ValuationSubring`, `open Field.absoluteGaloisGroup`, and
  `variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]` at lines 45–46);
- M249.019: docstring at lines 319–322, the `private theorem
  localSeparableResidueAlgAction_continuous` and its type at lines 323–327. Its
  proof (lines 327–379) is not part of this module.

The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution is also registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
Library's `notes/errata/` has no NYLL entry.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.localSeparableResidueAlgAction_continuous` (M249.019, private theorem; type) | `Langlands.NYLL.PortInternal.M249.d019Statement` (this module) |
| `LocalClassFieldTheory.residueAlgActionOfEqTop` (M244.003, used) | `Langlands.NYLL.LocalClassFieldTheory.residueAlgActionOfEqTop` (published, `...LocalReciprocity.ResidueActionIndex.U003.Definitions`) |
| `LocalClassFieldTheory.localSeparableValuationSubring` (M249.006, used) | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring` (published, `...LocalReciprocity.LocalResidueDatum.U006.Definitions`) |
| `LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top` (M249.010, used as a proof argument) | `Langlands.NYLL.LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top` (published proof, `...LocalReciprocity.LocalResidueDatum.U010.Proofs`) |

Row M249.019 of the published partition
[`notes/reuse/nyll-public-port/m241-m258.md`](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md)
reserves the name `Langlands.NYLL.PortInternal.M249.d019` for the private
source theorem, so the target is `Langlands.NYLL.PortInternal.M249.d019Statement`.
No declaration with this name exists in the current Library or Mathlib.

## Adaptation

The source theorem has no own binders; its only parameters are the section
variables `K` and its four instances. The target quantifies over exactly these,
in the source order and binder kinds, and the body after the `∀` is the source
type unchanged. The source docstring is kept on the target.

The changes are:

- the source theorem becomes a closed proposition `def` under the reserved
  `PortInternal` name, declared in `namespace Langlands.NYLL.PortInternal.M249`;
- the opens are reduced to `open Langlands.NYLL.LocalClassFieldTheory`, which
  supplies `residueAlgActionOfEqTop`, `localSeparableValuationSubring` and
  `localSeparableDecompositionGroup_eq_top`. The source opens of
  `ClassFormation`, `ValuationTheory`, `RamificationTheory`,
  `LocalFieldTheory`, `HilbertRamification.ValuationSubring`,
  `Field.absoluteGaloisGroup` and the scoped `Pointwise` and `ValuativeRel`
  notations provide nothing the type uses;
- the source imports are replaced by the two published modules
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U003.Definitions`
  (`residueAlgActionOfEqTop`, and through its imports the residue fields and
  their field and algebra instances) and
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U010.Proofs`
  (`localSeparableDecompositionGroup_eq_top`, and through its imports
  `localSeparableValuationSubring`). Every transitive import lies in the
  approved Mathlib environment or the published Library;
- the proof and all other source declarations are omitted.

## Instances used by the type

`IsGalois K (SeparableClosure K)` is Mathlib's instance for the separable
closure. The Krull topologies are Mathlib's `krullTopology` instances on
groups of field automorphisms. The field structure on `κ` and the `κ`-algebra
structure on `λ` are the published instances
`decompositionResidueField.instField` (M243.020) and
`selectedResidueField.instAlgebra` (M243.021).

## Development evidence and the proof unit

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). In a private probe (not part of
this candidate) the source proof, with the private source helpers
`localSelectedResidueLift` (M249.017, a chosen preimage under the residue map)
and `localSelectedResidueLift_residue` (M249.018) written as local `let` and
`have`, proves this exact target. That proof also uses the finiteness of `κ`
(the M249.014 instance `localDecompositionResidueFinite`, whose proof is routed
separately). The proof of this target is a separate `lean.proof@1` unit. This
is development evidence, not independent acceptance.

## Use downstream

The proof of this target becomes the `continuous_toFun` field of the
continuous residue action `localSeparableResidueAlgAction` (M249.020), a
continuous monoid homomorphism `Gal(Ω / K) →ₜ* (λ ≃ₐ[κ] λ)`. That definition
is published only after the proof.

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
