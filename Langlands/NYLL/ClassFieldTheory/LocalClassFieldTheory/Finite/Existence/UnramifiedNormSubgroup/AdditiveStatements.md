# Additive valuation modulo degree: proposition targets

This file states the four basic properties of the published homomorphism
`Langlands.NYLL.LocalClassFieldTheory.valuationModDegree K n`.
Every statement is a closed `def ... : Prop := ∀ ...`, with the source field
parameter `K : Type u` at arbitrary universe `u`, instance parameters
`[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`,
then `n : Nat`, and the source unit arguments in their original order.
There is no positive-degree or nonzero-degree assumption. In particular,
`ZMod 0` remains covered.

| Source unit | Target (after `Langlands.NYLL.LocalClassFieldTheory.`) | Meaning |
| --- | --- | --- |
| M266.002 | `valuationModDegree_applyStatement` | Evaluation of the reduced valuation is integer reduction of the published normalized unit valuation. |
| M266.003 | `valuationModDegree_surjectiveStatement` | Every element of ZMod n is a reduced normalized unit valuation. |
| M266.004 | `valuationModDegree_eq_zero_iff_dvdStatement` | The reduced valuation is zero exactly when the natural degree, cast to Int, divides the normalized unit valuation. |
| M266.005 | `valuationModDegree_eq_iff_dvd_subStatement` | Two reduced valuations agree exactly when the natural degree, cast to Int, divides the difference of the normalized unit valuations. |

The normalized integer-valued map is the published
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap`.
The evaluation and divisibility statements use this same map without a sign
change or replacement. The two-input statement uses the source ordered
difference `valuationMap K x - valuationMap K y`.
These definitions contain targets only; no property is asserted as a theorem
or taken as an axiom here.

## Source and changes

The original module is
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`
in Naganori Yamaguchi's ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
The full source was read; its SHA-256 is
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
It is registered in `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by that path.
No applicable errata entry was found in the project notes.

| Source declaration (after `LocalClassFieldTheory.`) | Source lines | Adapted declaration (after `Langlands.NYLL.LocalClassFieldTheory.`) |
| --- | --- | --- |
| `valuationModDegree_apply` | 37–41 | `valuationModDegree_applyStatement` |
| `valuationModDegree_surjective` | 44–50 | `valuationModDegree_surjectiveStatement` |
| `valuationModDegree_eq_zero_iff_dvd` | 53–59 | `valuationModDegree_eq_zero_iff_dvdStatement` |
| `valuationModDegree_eq_iff_dvd_sub` | 62–68 | `valuationModDegree_eq_iff_dvd_subStatement` |

Worker 205 added the namespace prefix and modification record, extracted
these related targets, changed each theorem into a closed Prop-valued
definition by universally quantifying its original telescope, and appended
`Statement` to its name. All mathematical expressions, universes, parameter
orders and hypotheses remain those of the source. Source theorem proofs
and simp attributes are reserved for proof contributions.
The sole import is the published M266.001 `UnramifiedNormSubgroup.U001.Definitions`;
the source's other module imports are unnecessary to state these targets.

The original copyright and author header is retained. Apache-2.0 license and
notices remain in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
No earlier adaptation or another worker's draft was reused.

The focused Lean-service check compiled this complete module with zero errors
and warnings in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`.
Inspection of `valuationModDegree_surjectiveStatement` confirmed
`statement_returns_prop: true`, universe `u`, and only the standard
`propext`, `Classical.choice`, and `Quot.sound` assumptions. The successful
focused compilation verifies that the published M266.001 data alone suffices
to state all four targets.
