# Renard VI.9.1, Remark 3, from uniform stabilization alone

Author: Worker 167, with Worker 5457 (author of the reduction module used here).

Module: `Langlands.Representation.Exponents.GeneralizedJacquetContractingRangeOfStabilization`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. VI.9.1, Remarque 3
and the paragraph of its proof beginning "Le troisième point résulte assez facilement du
deuxième" (printed p.198 / PDF p.204). That paragraph uses Théorème V.5.2 (printed p.123 /
PDF p.129).

## Statement

`GeneralizedJacquetContractingRangeOfStabilizationStatement.{u, v}` is the implication

```text
RationalPointFamily.UniformCompressionStabilizationStatement.{u, v} →
  GeneralizedJacquetContractingRangeStatement.{u, v}
```

between two unchanged published propositions, at the same universes `u` (field and group
schemes) and `v` (representation carriers).

- `RationalPointFamily.UniformCompressionStabilizationStatement` (module
  `Langlands.Representation.Exponents.UniformCompressionStabilizationStatement`) is the
  Proposition of VI.9.1 for the dynamic parabolic of a cocharacter. For a compact open `K` and
  an `M`-central Iwahori contraction `g`, it gives one exponent `b`, chosen before the
  representation. From `b` on, the power kernels and power ranges of the compressed action
  `A_g` on `V^K` are the kernel supremum `V^K_0` and the stable image `V^K_*`, and these two
  submodules are complementary.
- `GeneralizedJacquetContractingRangeStatement` (module
  `Langlands.Representation.Exponents.GeneralizedJacquetRemarksStatements`) is Remarque 3 for
  an actual rational parabolic `P = MN` with opposite `P̄ = MN̄`. For an `M`-central Iwahori
  contraction `t₀` of `K`, there is `ε > 0` such that for every `t ∈ A^+(ε)` and every smooth
  representation, `ker A_t = V^K_0(t₀)` and `Im A_t = V^K_*(t₀)`. It is the second target of
  task `7a03c792-1d54-4a95-89b7-dd1aa5e82a5e`.

The statement asserts neither proposition. It records that Remark 3 now depends only on the
Proposition of VI.9.1. The Proposition is the open target of task
`47e556e6-6b2a-40dc-ba66-d6a0585f5220`.

## Proof

`generalizedJacquetContractingRange_of_stabilization` proves the statement at arbitrary
universes `u, v`. It uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
Given the Proposition `hstab`, it applies the reduction theorem

```text
generalizedJacquetContractingRange_of_uniformStabilization :
  GeneralizedJacquetContractingRangeReductionStatement.{u, v}
```

(Worker 5457, module
`Langlands.Representation.Exponents.GeneralizedJacquetContractingRangeReduction`, candidate
`c1fdb671-5867-4467-b46e-cc08737c8e58`). The statement of that theorem is
`UniformCompressionStabilizationStatement.{u, v} → SplitComponentOppositeContractionStatement.{u} →
GeneralizedJacquetContractingRangeStatement.{u, v}`. The theorem is applied to `hstab` and to

```text
splitComponentOppositeContraction : SplitComponentOppositeContractionStatement.{u}
```

(module `Langlands.Representation.Exponents.SplitComponentOppositeContractionProof`, this
candidate). That theorem proves the two-sided uniform contraction of Renard V.5.2 (iii) on all
of `A^+(ε)`. Its Markdown describes the proof.

## Provenance

The implication as a single proposition is ours. Renard deduces Remarque 3 from the
Proposition, from Remarque 2 and from Théorème V.5.2. The reduction module uses V.5.2 (iii) as
Renard does. In place of the averages `e_C`, `e_C̄` of Remarque 2, it uses a factorization of
the compressed actions (its Markdown gives the details). The contraction module proves the form
of V.5.2 (iii) that the reduction takes as its second antecedent. The statement is recorded as
an intermediate result: the task's Remark 3 target still needs the Proposition of VI.9.1.
