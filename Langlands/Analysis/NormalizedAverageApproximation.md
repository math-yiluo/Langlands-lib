# Normalized averages near a point and right invariance under compact subgroups

Module `Langlands.Analysis.NormalizedAverageApproximation`, namespace
`Langlands.Analysis.NormalizedAverage`. Elementary measure-theoretic lemmas used to produce
nonzero averaged vectors.

## Results

- `integral_mem_of_isClosed`: a Bochner integral of an integrable function with values in a
  closed complex submodule `A` of a complete normed space lies in `A`. The integral commutes with
  the continuous quotient map by `A`, which kills every value.
- `norm_integral_smul_sub_le`: let `a` be an integrable complex weight with `∫ a = 1` and
  `∫ ‖a‖ = 1`. Let `o` be a vector-valued function with `a • o` integrable. If
  `‖o(y) - v‖ ≤ ε` wherever `a(y) ≠ 0`, then `‖∫ a • o - v‖ ≤ ε`. Write `∫ a • o - v` as
  `∫ a • (o - v)` and bound by `∫ ‖a‖ ε`.
- `integral_smul_ne_zero`: under the same hypotheses with `ε = ‖v‖ / 2` and `v ≠ 0`, the
  average `∫ a • o` is nonzero.
- `exists_normalized_bump`: on a locally compact Hausdorff space with a measure that is finite
  on compacts and positive on nonempty open sets, every neighbourhood `U` of a point `y₀`
  contains the support of a compactly supported continuous complex weight `a` with `∫ a = 1`
  and `∫ ‖a‖ = 1`. Urysohn's lemma (`exists_continuousMap_one_of_isCompact_subset_isOpen`) gives
  a bump with values in `[0, 1]`, equal to `1` at `y₀`. Its integral is positive, and dividing
  by it normalizes the weight.
- `map_mul_right_eq_self_of_isCompact`: let `G` be a second countable, locally compact
  Hausdorff group and `μ` a left Haar measure. Then right translation by an element `k` of a
  compact subgroup `K` preserves `μ`. By uniqueness of Haar measure
  (`Measure.isMulLeftInvariant_eq_smul`), the image of `μ` under right translation by `k` is
  `c • μ`. Take a compact neighbourhood `V` of the identity. The set `V K` is compact, has
  positive measure, and is fixed by right translation by `k`. Evaluating both measures on it
  gives `c = 1`.

## Provenance

Standard facts of harmonic analysis: approximate identities, Urysohn's lemma, and the
triviality of the modular function on compact subgroups. The proofs here are direct and use
Mathlib's Urysohn lemma and uniqueness of Haar measure.
