# Comparing a Haar measure with a transported Haar measure

Lean module: `Langlands.Representation.Intertwining.HaarTransportComparison`.

This module supplies the measure-theoretic step of Renard VII.3.5 (ii), clause 1: the Haar
measure on `V = N̄₁(F) ∩ N₂(F)` that corresponds to a Haar measure on
`V' = N̄₁'(F) ∩ N₂'(F)` is the image measure under the identification `V' ≃ V`. Renard uses
this tacitly when he says the measures are "compatible"; the statements here are generic
facts about topological groups and are internal helpers, not results from the literature.

## Declarations

- `exists_isCompact_openSubgroup`: a locally compact nonarchimedean group `G` has an open
  subgroup `K` that is compact. Proof: take a compact neighbourhood `C` of `1`; the
  nonarchimedean property gives an open subgroup `K ⊆ C`; open subgroups are closed, so `K`
  is compact as a closed subset of `C`.
- `haar_eq_map_of_measure_eq`: in a locally compact second countable group `H`, if a Haar
  measure `haar` and the image `haar'.map e` of a Haar measure under a topological group
  isomorphism `e : H' ≃ₜ* H` take the same value on one nonempty compact open set `S`, then
  `haar = haar'.map e`. Proof: Mathlib's uniqueness of Haar measures in second countable
  groups (`Measure.isMulLeftInvariant_eq_smul`) gives `haar = c • haar'.map e`; evaluating at
  `S`, where the image measure is nonzero (nonempty open) and finite (compact), forces `c = 1`.
- `integral_map_continuousMulEquiv`: `∫ φ d(haar'.map e) = ∫ φ ∘ e dhaar'`, from
  `integral_map_equiv` applied to the measurable equivalence underlying `e`.
- `map_isHaarMeasure_integral_eq`: for `V` a subgroup of `G` and `e : H' ≃ₜ* V`, the image
  measure `haar'.map e` is a Haar measure on `V` and `∫ φ(e x) dhaar'(x) = ∫_V φ d(haar'.map e)`
  for every `φ : G → ℂ`. This is the existence half of clause 1.
- `haar_eq_map_of_integral_eq`: let `G` be locally compact, second countable and
  nonarchimedean, `V` a closed subgroup with a Borel σ-algebra, and `e : H' ≃ₜ* V`. If a Haar
  measure `haar` on `V` satisfies `∫ φ(e x) dhaar'(x) = ∫_V φ dhaar` for every continuous
  compactly supported `φ : G → ℂ`, then `haar = haar'.map e`. Proof: `V` is locally compact
  (closed in `G`) and second countable (subspace). Take a compact open subgroup `K` of `G`;
  its indicator `φ` is continuous (clopen) and compactly supported. On `V` it is the
  indicator of `S = V ∩ K`, which is open, compact (closed embedding of `V`) and contains `1`.
  The hypothesis for this `φ` and `integral_indicator_const` give equal real measures of `S`;
  both are finite, so `haar S = (haar'.map e) S`, and `haar_eq_map_of_measure_eq` concludes.
