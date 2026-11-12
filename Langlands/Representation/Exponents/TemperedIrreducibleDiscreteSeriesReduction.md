# The VII.2.6 Theorem (existence) and Corollary from named inputs

Author: Worker 4772. This is an internal reduction for proof task
`225f7d3d-bb91-4746-9084-ea6b91241e41`. It concerns Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, VII.2.6, Theorem, first assertion (printed p.231 / PDF p.237),
and its Corollary (printed p.232 / PDF p.238). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The module derives the exact published propositions
`TemperedIrreducibleDiscreteSeriesStatement` and
`TemperedIrreducibleUnitarizableStatement` from other published
propositions, which appear as explicit hypotheses. It proves none of those
hypotheses. So it is not a proof of either VII.2.6 proposition, and it says
nothing about the uniqueness assertion
`TemperedIrreducibleDiscreteSeriesUniquenessStatement`.

## Inputs

All inputs are published `Prop` declarations, used unchanged at the
universes of the targets: `u` for the field, `v` for the carrier.

| Hypothesis | Published proposition | Source |
| --- | --- | --- |
| `hSq` | `SquareIntegrableNormalizedTemperedStatement.{u, v}` | VII.2.1, Remark 2 |
| `hInd` | `LeviInductionNormalizedTemperedStatement.{u, v}` | VII.2.2, Lemma |
| `hCompact` | `ArbitraryParabolicQuotientCompactStatement.{u}` | V.5.1, Corollary (compactness part) |
| `hSI` | `TemperedSquareIntegrableUnitaryPartStatement.{u, v}` | VII.2.4, Lemma |
| `hUnimod` | `RationalPointFamily.RationalReductiveUnimodularityStatement.{u}` | unimodularity of `G(F)` |
| `hStandard` | `StandardCocharacterStatement.{u}` | premise of `hUnimod` |

## Declarations

`isNormalizedExponentTempered_of_squareIntegrable_induction_embedding`
proves sufficiency. Assume `hSq` and `hInd`. Let `p, l, r` be an actual
parabolic, rational Levi and matching radical with their multiplication
isomorphism. Let `σ` be a smooth representation of `M(F)` (with
`leviPointTopology`) that is square-integrable modulo the center for every
measurable structure, Borel structure and Haar measure on
`M(F) ⧸ Subgroup.center M(F)`. If `f` is an injective intertwiner from `π`
into `(leviInductionFunctor p l r hp hr hl hmul).obj σ`, then `π` is
normalized-exponent tempered. Irreducibility of `σ` is not needed.

`temperedIrreducibleDiscreteSeries_of_inputs` proves
`TemperedIrreducibleDiscreteSeriesStatement.{u, v}` from `hSq`, `hInd`,
`hCompact` and `hSI`. The entry declaration
`temperedIrreducibleDiscreteSeriesOfInputs` is a definition whose type is
the same implication, curried in that order. Its value is this theorem.

`temperedIrreducibleUnitarizable_of_discreteSeries` proves
`TemperedIrreducibleUnitarizableStatement.{u, v}` from
`TemperedIrreducibleDiscreteSeriesStatement.{u, v}`, `hUnimod`, `hStandard`
and `hCompact`. `temperedIrreducibleUnitarizable_of_inputs` composes the two
theorems, so the Corollary follows from the six inputs of the table.

## Proofs

Sufficiency follows Renard's argument. The quotient `M(F) ⧸ Z(M(F))` gets
the Borel measurable structure and Mathlib's Haar measure
`MeasureTheory.Measure.haar`. `M(F)` is Hausdorff for its canonical
topology, by `rationalPoint_t2Space`. `σ` is square-integrable for this
measure, so `hSq`, applied to the connected reductive group `M`, makes `σ`
normalized-exponent tempered. Then `hInd` makes the normalized induction
tempered. The published
`IsNormalizedExponentTempered.of_injective_intertwining` passes
temperedness back along the injective `f`, across the carrier universes `v`
and `max u v`.

For the existence assertion, the forward direction is
`IsNormalizedExponentTempered.exists_squareIntegrable_induction_embedding`
from `TemperedMinimalSquareIntegrable`, which uses `hCompact` and `hSI`.
The reverse direction is the sufficiency theorem, which does not use the
irreducibility of `σ`.

The Corollary is Worker 346's published constructor
`temperedIrreduciblePresentationForm`. It produces an
`InvariantPositiveForm` on any irreducible tempered `π`, from the existence
assertion, `hUnimod`, `hStandard` and `hCompact`, and `IsUnitarizable` is
the existence of such a form. That constructor follows Renard's proof of
the Corollary. It takes the discrete-series embedding, gives `σ` an
invariant form through its square-integrable coefficients, induces the
form over the compact quotient, and restricts it along the embedding.

## Scope

All field, valuation, topology, local-field, connected-reductive,
local-compactness and nonarchimedean-group quantifiers of the targets are
kept. Parabolics are arbitrary actual rational parabolics. Square-integrability
is quantified over all Haar measures, as in the target. No standardness,
admissibility, finite-length, central-character, presentation-existence,
Jacquet-admissibility or Iwahori-contraction hypothesis is added beyond the
six listed propositions. Their proofs are the subject of other tasks:
`1ebce298-eeeb-4686-ba30-cabcb8e50d4b` (VII.2.1 Remark 2),
`f83123b9-ff38-4210-9ad7-4f119a13d1ac` (VII.2.2),
`c1ce4629-6768-4eb5-b4ee-0086526913ea` (quotient compactness) and
`f0ff1d42-b2ac-439b-a08d-8e2d120a78fa` (VII.2.4 Lemma).
