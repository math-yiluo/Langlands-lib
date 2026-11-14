# Residue fields of the chosen separable valuation ring: instance targets

This module states NYLL source units M249.014 and M249.016 as closed
propositions. Each source declaration is an `instance` whose class is a
proposition. The module exports two Prop-valued `abbrev`s in namespace
`Langlands.NYLL.LocalClassFieldTheory`:

- `localDecompositionResidueFiniteStatement` (M249.014);
- `localSelectedResidueIsAlgClosedStatement` (M249.016).

Nothing is proved here, and no instance is installed. Each proof is a
separate unit under the adapted source name
(`Langlands.NYLL.LocalClassFieldTheory.localDecompositionResidueFinite` and
`Langlands.NYLL.LocalClassFieldTheory.localSelectedResidueIsAlgClosed`). Such
a unit may register its proof as a global instance, as in the source.

Mathematically, let `K` be a nonarchimedean local field and let `B` be the
valuation ring `localSeparableValuationSubring K` of the separable closure
`K^sep` chosen in M249.006. Let `Z` be the decomposition group of `B` over
`K`. The targets say:

- M249.014: the residue field `κ` of the fixed subring `B^Z` is finite;
- M249.016: the residue field `λ = B/𝔪_B` of `B` is algebraically closed.

## The propositions

```lean
abbrev localDecompositionResidueFiniteStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    Finite (decompositionResidueField K
      (localSeparableValuationSubring K))

abbrev localSelectedResidueIsAlgClosedStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    IsAlgClosed (selectedResidueField
      (localSeparableValuationSubring K))
```

There is no level parameter: `K` lives in `Type`, as in the source. The
quantified binders, in order, are the section variables of the source (lines
45–46). Neither source instance has parameters of its own.

| Binder | Meaning |
| --- | --- |
| `K : Type` | the base field |
| `[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]` | `K` is a nonarchimedean local field (Mathlib's class) |

In M249.014 the conclusion is Mathlib's class `Finite` for the type
`decompositionResidueField K B`. That type is the quotient of the fixed
subring `B^Z` of `B` by the contraction of the maximal ideal of `B`. In
M249.016 the conclusion is Mathlib's class `IsAlgClosed` for the field
`selectedResidueField B`, which is `IsLocalRing.ResidueField B`.

### Published declarations used

- `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring K`
  (M249.006, [definition](../U006/Definitions.md)): the preimage, under the
  inclusion `SeparableClosure K → AlgebraicClosure K`, of a valuation subring
  of `AlgebraicClosure K` chosen by Chevalley's extension theorem.
- `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField`
  (M243.003) and `...selectedResidueField` (M243.004),
  [definitions](../../../../../../ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence/Definitions.md):
  for a Galois extension `L/K` and a valuation ring `A` of `L`, the residue
  field `κ` of the fixed subring of the decomposition group of `A`, and the
  residue field `λ` of `A`. Here `L = SeparableClosure K`. The Galois instance
  `IsGalois K (SeparableClosure K)` that `decompositionResidueField` needs is
  Mathlib's.

The statements need neither of the local instances M249.001 and M249.002.

### Why the targets are `abbrev`s

The source registers M249.014 and M249.016 as global instances. Following the
Library's convention for Prop-valued instances (for example M249.008 in the
[U008 target](../U008/Statements.md)), each target is a reducible `abbrev`.
A theorem whose type is the target can then be given `attribute [instance]`.
Instance search unfolds the `abbrev` and sees the `∀`-telescope ending in the
class. A private probe compiled together with this module (diagnostic
`7a29273f`) checked two things. A toy closed-`∀` `abbrev` proved by a theorem
and given `attribute [instance]` is found by `inferInstance`. A hypothesis of
type `localDecompositionResidueFiniteStatement`, applied to `K` with
`haveI := h K`, lets `infer_instance` prove
`Finite (decompositionResidueField K (localSeparableValuationSubring K))`.

## Check

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), against Library
commit `c40a01345b2f4172fa41e07ff31644b40e695003`, compiled the module with no
errors or warnings. Inspection reported, for each declaration, kind
`definition`, no level parameters, `statement_returns_prop: true`, and only the
axioms `propext`, `Classical.choice` and `Quot.sound`:

| Declaration | Diagnostic |
| --- | --- |
| `localDecompositionResidueFiniteStatement` | `c5188284-5cb4-4120-873b-86694f9472f3` |
| `localSelectedResidueIsAlgClosedStatement` | `d0ac1e77-6636-42e8-9a1e-ebb254f05dbb` |

## Imports and scope

The imports are the published modules
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions`
(for `localSeparableValuationSubring`) and
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Definitions`
(for `decompositionResidueField` and `selectedResidueField`), and Mathlib's
`Mathlib.FieldTheory.IsAlgClosed.Basic` (for `IsAlgClosed`).

Only M249.014 and M249.016 are stated. Between them in the source is the
instance M249.015 `localDecompositionResidueFintype` (lines 262–266). Its
class `Fintype` is data, not a proposition, so it is not a statement target.
Its source body is `Fintype.ofFinite _`, which uses M249.014. It is left for a
separate definition unit once a proof of M249.014 is published.

The source proofs are not ported here. The M249.014 proof transports
finiteness of the residue field of `K` along the equivalence
`localBaseResidueEquivDecompositionResidue` (M249.012), which is not yet
published. The M249.016 proof compares `λ` with the residue field of the
chosen valuation ring of `AlgebraicClosure K`.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean#L252-L271)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, readable in the project
snapshot under `n-yamaguchi-0729--ClassFieldTheory/source/`. The full file has
SHA-256 `be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`, the
value recorded for M249 in the
[public declaration partition](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m249).

| Partition unit | Original declaration in `LocalClassFieldTheory` | Original lines | Adapted target in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- | --- | --- |
| M249.014 | instance `localDecompositionResidueFinite` | 252–255 (body 256–260) | `localDecompositionResidueFiniteStatement` |
| M249.016 | instance `localSelectedResidueIsAlgClosed` | 268–271 (body from 271) | `localSelectedResidueIsAlgClosedStatement` |

For each unit the first listed line is the doc comment, the next line the
instance name, and the following lines its type. The source module opens
namespace `LocalClassFieldTheory` (line 31), opens
`HilbertRamification.ValuationSubring` (line 42) after opening
`RamificationTheory` (line 35), works in `noncomputable section` (line 39) and
declares the section variables at lines 45–46.

Worker 85 made these changes on 14 November 2026:

- added the `Langlands.NYLL` prefix to the namespace and to the opened
  namespace, which becomes
  `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`;
- packaged each instance type as a closed proposition, as a reducible
  `abbrev` with the suffix `Statement`. The section variables become the
  leading `∀`-binders, with the same kinds (explicit for `K`,
  instance-implicit for the rest);
- omitted the source bodies, the `instance` attributes and the
  `noncomputable` modifier, the other `open` lines, and all other
  declarations;
- replaced the source imports by the published modules above and Mathlib's
  `IsAlgClosed` module.

No draft from another worker was used.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The partition records no patch10 change to `LocalResidueDatum.lean`.

The Lean file keeps the original copyright and author header verbatim
(copyright 2026 Naganori Yamaguchi; authors Naganori Yamaguchi, assisted by
OpenAI Codex) and records the modifications. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are unchanged in the
Library, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
