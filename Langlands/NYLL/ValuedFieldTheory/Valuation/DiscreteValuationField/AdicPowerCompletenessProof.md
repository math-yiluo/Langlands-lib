# Completeness from a positive power of an ideal

The entry module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.AdicPowerCompletenessProof`
proves NYLL M105.013 as the single theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.isAdicComplete_of_isAdicComplete_pow.{u, v}`.
Its complete unapplied type is exactly the published closed proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.IsAdicCompleteOfIsAdicCompletePowStatement.{u, v}`.
The theorem has only the independent universe parameters `u` and `v`.
It imports the unchanged statement from
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.MaximalIdealCompletenessStatements`.

## Exact mathematical content

The proposition expands to

```lean
∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
  (I : Ideal R) {n : ℕ} (hn : 0 < n) [IsAdicComplete (I ^ n) M],
  IsAdicComplete I M
```

Here `R` is any commutative ring and `M` is any additive commutative group
with the supplied `R`-module action. For the same ideal `I` and a strictly
positive natural exponent `n`, completeness for `I ^ n` implies completeness
for `I`. The ring and module universes are independent. No Noetherianity,
finite generation, nontriviality, field, valuation, algebra or additional
topological structure is assumed. The structures and module action are the
same throughout the proof.

`IsAdicComplete` is Mathlib's actual class from
`Mathlib.RingTheory.AdicCompletion.Basic`, extending `IsHausdorff` and
`IsPrecomplete`. Its defining congruences are modulo the actual submodules
`I ^ k • ⊤ : Submodule R M`. Hausdorffness says that an element congruent to
zero modulo every such submodule equals zero. Precompleteness gives a limit
for each sequence `f : ℕ → M` satisfying
`f a ≡ f b [SMOD (I ^ a • ⊤)]` whenever `a ≤ b`.

## Implemented proof

The proof introduces all the proposition's internal parameters and constructs
the two fields of `IsAdicComplete I M` by local arguments.

For the local proof `hhaus`, let `x` be congruent to zero modulo `I ^ k • ⊤`
for every `k`. Testing this at `n * k` gives congruence modulo
`(I ^ n) ^ k • ⊤`, using `pow_mul`. The supplied completeness instance for
`I ^ n` supplies its Hausdorff field, so `IsHausdorff.haus` gives `x = 0`.
This local argument does not need positivity.

For the local proof `hprec`, start with a compatible sequence `f` for `I`.
The subsequence `g k := f (n * k)` is compatible for `I ^ n`: multiplication
by `n` preserves inequalities, and `pow_mul` identifies its congruence
submodules. The supplied precompleteness field gives `L : M` with
`f (n * k) ≡ L` modulo `I ^ (n * k) • ⊤`.

For each original index `m`, strict positivity gives `1 ≤ n` and hence
`m ≤ n * m`. Compatibility therefore gives
`f m ≡ f (n * m)` modulo `I ^ m • ⊤`.
Mathlib's `Submodule.pow_smul_top_le I M` gives
`I ^ (n * m) • ⊤ ≤ I ^ m • ⊤`; `SModEq.mono` weakens the subsequence's
limit congruence to this modulus. Transitivity yields
`f m ≡ L` modulo `I ^ m • ⊤`. This is exactly precompleteness for `I`.
Finally the proof combines `hhaus` and `hprec` into `IsAdicComplete I M`.

No supporting declaration or new global instance is exported. The later
integral-closure maximal-ideal completeness target M245.014 is a separate
proof unit.

## Source correspondence and modifications

The original is Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/AdicPower.lean`.
Worker 384 read lines 1–27 and 203–253, including the ambient variables and
all three source arguments. The source declaration map is:

| Source declaration in `ValuationTheory.DiscreteValuationField` | Source lines | Adapted implementation |
| --- | --- | --- |
| `isHausdorff_of_isHausdorff_pow` (M105.011) | 204–213 | Local proof `hhaus` in the final theorem |
| `isPrecomplete_of_isPrecomplete_pow` (M105.012) | 215–243 | Local proof `hprec` in the final theorem |
| `isAdicComplete_of_isAdicComplete_pow` (M105.013) | 245–252; ambient variables 22–24 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.isAdicComplete_of_isAdicComplete_pow` |

The mathematical route is the source route. The adaptation prefixes the
namespace with `Langlands.NYLL`, imports the already published closed
statement instead of the original `AdicCompletion.Functoriality` import,
and moves all mathematical parameters inside the named proposition.
The theorem explicitly retains the independent universe levels `u, v`.
The two small source helpers become local proofs, and the unrelated
declarations and unused ambient module `N` are omitted.
The same Mathlib congruence, natural-number inequality and ideal-power
monotonicity lemmas implement the argument in the approved environment.
The published statement and its dependencies are unchanged.

Current Library and Mathlib searches found no existing proof of this target.
The Library's
`Langlands.Cohomology.DivisibleSystem.isAdicComplete_of_le_of_pow_le`
transfers completeness in the other direction and is not used here.

## Attribution and retained sources

Registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The pinned readable file is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its verified SHA256 is
`df1f92c6b85a87ad4a27c319302f267a717b7f82c1cce10167c56b1c4793232d`.

Registered attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement` has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Its manifest and ValuedFieldTheory source table, and the upstream NOTICE,
contain no source-specific entry for `AdicPower.lean`. No applicable project
erratum was found in the workspace, project notes or Library notes.

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi; authors Naganori Yamaguchi (assisted by OpenAI
Codex); Apache-2.0. The unchanged
[LICENSE](../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../licenses/NYLL/NOTICE) accompany the adaptation.
Worker 384 wrote this focused proof adaptation and its Markdown on
30 October 2026, recording the modifications in the Lean header.
Worker 106 supplied routing and source observations, with no implementation
draft. Published dependencies are imported by Lean name.

The approved environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`; upstream used
Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
