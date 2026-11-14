# The base residue field of the chosen separable valuation ring (M249.011, M249.012)

Let `K` be a nonarchimedean local field (a field with `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField` instances). Finite local
reciprocity fixes a valuation ring `A = localSeparableValuationSubring K` of
the separable closure `K^sep = SeparableClosure K`. Its valuation extends the
canonical complete discrete valuation `localCompleteDVF K` of `K`. Every
`K`-automorphism of `K^sep` maps `A` onto itself, so the decomposition group
of `A` over `K` is the whole Galois group. Hence the decomposition field `Z`
of `A`, the fixed field of that group, is `K` itself.

This module records two consequences of `Z = K`:

- `Langlands.NYLL.PortInternal.M249.d011 K` (source unit M249.011, a private
  definition in the source) is a ring equivalence from the valuation ring of
  `localCompleteDVF K` to the valuation ring `A ∩ Z` of the decomposition
  field. It sends `x` to `x` viewed as an element of `Z`. Its value in
  `K^sep` is `algebraMap K (SeparableClosure K) x`.
- `Langlands.NYLL.LocalClassFieldTheory.localBaseResidueEquivDecompositionResidue K`
  (source unit M249.012) is a ring equivalence from the residue field of
  `localCompleteDVF K` to `decompositionResidueField K A`. That field is the
  residue field of the decomposition field used by the residue-action exact
  sequence. The equivalence is `d011 K` on residue fields followed by the
  published comparison `decompositionFieldResidueEquiv` (M243.018).

In Lean, with `variable (K : Type) [Field K] [ValuativeRel K]
[TopologicalSpace K] [IsNonarchimedeanLocalField K]`:

```lean
noncomputable def Langlands.NYLL.PortInternal.M249.d011 :
    (localCompleteDVF K).valuationSubring ≃+*
      decompositionFieldValuationSubring K
        (localSeparableValuationSubring K)

noncomputable def Langlands.NYLL.LocalClassFieldTheory.localBaseResidueEquivDecompositionResidue :
    (localCompleteDVF K).residueField ≃+*
      decompositionResidueField K (localSeparableValuationSubring K) :=
  (IsLocalRing.ResidueField.mapEquiv
      (Langlands.NYLL.PortInternal.M249.d011 K)).trans
    (decompositionFieldResidueEquiv (K := K)
      (localSeparableValuationSubring K))
```

The body of `d011` is a tactic proof that builds the equivalence; the code
block shows only its type.

## The objects involved

- `localCompleteDVF K : CompleteDVF K` is the canonical complete discrete
  valuation of `K` (module
  `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.Canonical`).
  `(localCompleteDVF K).valuationSubring` and
  `(localCompleteDVF K).residueField` are the published `CompleteDVF`
  projections (module
  `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections`):
  its valuation ring and the residue field of that ring.
- `localSeparableValuationSubring K : ValuationSubring (SeparableClosure K)`
  is the chosen valuation ring `A` (M249.006, module
  `...LocalReciprocity.LocalResidueDatum.U006.Definitions`).
- In the namespace
  `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`:
  `decompositionGroup K A` is the subgroup of `K`-automorphisms `σ` with
  `σ • A = A` (M239.001); `decompositionField K A` is its fixed intermediate
  field `Z` (M239.011);
  `decompositionFieldValuationSubring K A = A.comap (decompositionField K A).val`
  is the valuation ring `{z ∈ Z | (z : K^sep) ∈ A}` (M243.005); and
  `decompositionResidueField K A` is the base residue field `κ` of the
  residue-action exact sequence: the quotient of the subring of `A` fixed by
  the decomposition group by the contraction of the maximal ideal of `A`
  (M243.003).
- `decompositionFieldResidueEquiv (K := K) A` is the published ring
  equivalence from the residue field of `decompositionFieldValuationSubring K A`
  to `decompositionResidueField K A` (M243.018, module
  `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueComparison`).

## How the body of `d011` builds the equivalence

The body uses two published theorems about the chosen ring:

- `localSeparableDecompositionGroup_eq_top` (M249.010, module
  `...LocalResidueDatum.U010.Proofs`): for every such `K`,
  `decompositionGroup K (localSeparableValuationSubring K) = ⊤`;
- `localSeparableValuationSubring_pullback` (M249.007, module
  `...LocalResidueDatum.U007.Proofs`): for `x : K`,
  `algebraMap K (SeparableClosure K) x ∈ localSeparableValuationSubring K` if
  and only if `x` lies in the valuation ring of `(localCompleteDVF K).valuation`.

Both are proved against closed targets that quantify over `K`, so the body
applies them to `K` (and `x`).

Write `A` for the chosen ring and `Z` for `decompositionField K A`. The body
first proves `hZ : Z = ⊥`. Since `Z` is by definition
`IntermediateField.fixedField (decompositionGroup K A)`, M249.010 rewrites it
to `IntermediateField.fixedField ⊤`. Mathlib's
`InfiniteGalois.fixedField_fixingSubgroup ⊥` states that the fixed field of
the fixing subgroup of `⊥` is `⊥`; `simpa` identifies that fixing subgroup
with `⊤`. This uses that `SeparableClosure K` is Galois over `K`, an instance
supplied by Mathlib.

It then sets `eKZ : K ≃ₐ[K] Z`. This is Mathlib's
`(IntermediateField.botEquiv K (SeparableClosure K)).symm`, identifying `K`
with the bottom intermediate field, followed by
`IntermediateField.equivOfEq hZ.symm`. For `x : K`, the value of `eKZ x` in
`K^sep` is `algebraMap K (SeparableClosure K) x`, by `rfl`.

The equivalence sends `x` to `⟨eKZ x, _⟩`; the inverse sends `z` to
`⟨eKZ.symm z, _⟩`. Both round trips, additivity and multiplicativity follow
from the same facts for `eKZ`, applied under `Subtype.ext`. The two membership
proofs are:

- `eKZ x` lies in `decompositionFieldValuationSubring K A`: its value in
  `K^sep` is `algebraMap K (SeparableClosure K) x`, which lies in `A` by the
  backward direction of M249.007, since `x` is in the valuation ring of `K`;
- `eKZ.symm z` lies in the valuation ring of `K`: by the forward direction of
  M249.007 it suffices that `algebraMap K (SeparableClosure K) (eKZ.symm z)`
  lies in `A`. That element equals the value of `z` in `K^sep`, which lies in
  `A` because `z` is in `decompositionFieldValuationSubring K A`.

The membership proofs are propositions. The underlying functions are fixed:
forward, `x ↦ eKZ x`, with value `algebraMap K (SeparableClosure K) x` in
`K^sep`; backward, its inverse.

## The residue-field equivalence

`localBaseResidueEquivDecompositionResidue K` is the composite of two ring
equivalences. The first is Mathlib's `IsLocalRing.ResidueField.mapEquiv`
applied to `d011 K`: the ring equivalence of residue fields induced by the
local ring equivalence `d011 K`. Its codomain is the residue field of
`decompositionFieldValuationSubring K A`. The second is
`decompositionFieldResidueEquiv (K := K) A`. So a residue class of an
integer `x` of `K` goes first to the residue class of `x` viewed in
`A ∩ Z`, and then to its class in `decompositionResidueField K A`.

## Binders and universes

Both declarations take the explicit field `(K : Type)` and the instance
binders `[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]` of the source section variables. `K` lives in
`Type`, as in the source. Neither declaration has universe parameters.

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
- M249.011: docstring at lines 178–179, private definition and body at
  lines 180–223;
- M249.012: docstring at lines 225–226, definition and body at lines
  227–233.

The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution is also registered
as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Library's `notes/errata/` has no NYLL entry.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.localBaseValuationSubringEquivDecompositionField` (M249.011, private) | `Langlands.NYLL.PortInternal.M249.d011` (this module) |
| `LocalClassFieldTheory.localBaseResidueEquivDecompositionResidue` (M249.012) | `Langlands.NYLL.LocalClassFieldTheory.localBaseResidueEquivDecompositionResidue` (this module) |
| `LocalClassFieldTheory.localSeparableValuationSubring` (M249.006, used) | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring` (published) |
| `LocalClassFieldTheory.localSeparableValuationSubring_pullback` (M249.007, used) | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_pullback` (published proof of `localSeparableValuationSubring_pullbackStatement`) |
| `LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top` (M249.010, used) | `Langlands.NYLL.LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top` (published proof of `localSeparableDecompositionGroup_eq_topStatement`) |
| `RamificationTheory.HilbertRamification.ValuationSubring.decompositionFieldResidueEquiv` (M243.018, used) | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFieldResidueEquiv` (published) |

Rows M249.011 and M249.012 of the published partition
[`notes/reuse/nyll-public-port/m241-m258.md`](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md)
reserve these two adapted names and the module stem
`Langlands/NYLL/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum`.
Neither name exists in the current Library or Mathlib.

## Imports and modification record

The direct imports are the published modules
`...LocalReciprocity.LocalResidueDatum.U007.Proofs` (M249.007, which imports
the definition of `localSeparableValuationSubring`),
`...LocalReciprocity.LocalResidueDatum.U010.Proofs` (M249.010),
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueComparison`
(M243.018, which imports the definitions of the decomposition group, field,
valuation ring and residue field) and
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections`
(the `CompleteDVF` projections). They replace the source's four imports
(`ResidueActionIndex`, `FiniteIntegralClosure`,
`FiniteExtensionCorrespondence` and `FiniteExtensionCompleteDVF`), which
serve the other declarations of the source file. Every transitive import lies
in the approved Mathlib environment or the published Library.

Worker 85 extracted these two source definitions on 14 November 2026. The
Lean header records the change. The changes are:

- the private source definition M249.011 is a public definition named
  `Langlands.NYLL.PortInternal.M249.d011`, the port-internal name reserved by
  the partition, in its own namespace block. Its docstring is prefixed with
  `M249.011 (source private localBaseValuationSubringEquivDecompositionField):`
  and otherwise unchanged; its type and tactic body (lines 181–223, compared
  line by line) are unchanged;
- M249.012 is in the namespace `Langlands.NYLL.LocalClassFieldTheory`. Its
  docstring, type and body are unchanged, except that the body refers to the
  port-internal name `Langlands.NYLL.PortInternal.M249.d011 K` in place of
  `localBaseValuationSubringEquivDecompositionField K`;
- the imports are replaced as described above;
- the source opens are replaced by fully qualified opens of
  `Langlands.NYLL.LocalFieldTheory` (for `localCompleteDVF`),
  `Langlands.NYLL.LocalClassFieldTheory` (in the `d011` block, for the chosen
  ring and the two theorems) and
  `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`.
  The opens of `ClassFormation`, `ValuationTheory`, `Field.absoluteGaloisGroup`
  and the scoped `Pointwise` and `ValuativeRel` notation provide nothing these
  definitions use, and are omitted.

The source's two local instances (M249.001, M249.002) are not needed by these
definitions and are not activated. Every other source declaration is
omitted. In particular the naturality lemma
`localBaseResidueEquivDecompositionResidue_algebraMap` (M249.013, proved by
`rfl` in the source) and the instances M249.014–M249.016 are not part of this
module. No theorem, instance, notation or alias is introduced.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection reports both
declarations as definitions without level parameters, depending only on the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. This
development check is not independent acceptance.

## Use downstream

In the source, `localBaseResidueEquivDecompositionResidue` is used by:

- the naturality lemma M249.013 (source lines 235–250), proved by `rfl`;
- the instance M249.014 `localDecompositionResidueFinite`, which transfers
  finiteness of the residue field of `K` along this equivalence. Its closed
  target `localDecompositionResidueFiniteStatement` is already published
  (module `...LocalResidueDatum.U014.Statements`);
- the residue-degree comparison M252.004.

A development probe (not part of this candidate) checked the M249.013
statement by `rfl` and proved the M249.014 target with
`Finite.of_equiv _ (localBaseResidueEquivDecompositionResidue K).toEquiv`
against this module.

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex); Apache-2.0. The original
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain in `licenses/NYLL/`. Worker 85 adapted these units directly from the
pinned original; no other project worker supplied code.
