# Haar and Lp comparison for a compact-kernel quotient

This is an internal analytic target, motivated by the comparison between the
actual quotients `G/A` and `G/Z(G)` in the Waldspurger program. It is not
attributed to a separate assertion in Waldspurger, and it is not a reductive
structural input. This file defines propositions; it supplies no proof.

`Langlands.CompactKernelProperMapStatement` concerns a continuous group
homomorphism `q : G → H` between locally compact Hausdorff topological groups.
It states that surjectivity, openness and compactness of the actual homomorphism
kernel imply that `q` is a proper map, in Mathlib's `IsProperMap` sense.
Neither a Haar measure nor second countability is needed in this target.

`Langlands.CompactKernelHaarLpMeasureStatement` uses the same group hypotheses,
their Borel measurable structures, and second countability of `H`. For any
supplied Haar measures `μ` on `G` and `ν` on `H`, it states all of the following:

- The actual pushforward `Measure.map q μ` is a Haar measure on `H`.
- There is a strictly positive finite real number `C` such that
  `Measure.map q μ = ENNReal.ofReal C • ν`.
- For every continuous `f : H → E` into any normed additive commutative group
  and every extended nonnegative real exponent `p`, `f ∘ q` belongs to `Lᵖ(μ)`
  exactly when `f` belongs to `Lᵖ(ν)`. Membership means Mathlib's `MemLp`,
  including almost-everywhere strong measurability.

`Langlands.CompactKernelHaarLpComparisonStatement` is the conjunction of these
two targets. The universes of `G`, `H`, and `E` are independent. The map,
kernel, pushforward and pullback are the actual ones; no measure is chosen to
force preservation. The scalar is allowed to depend on the map and the chosen
measures. No probability normalization or measure-preserving assertion is made.

The intended proof route is compact-kernel quotient topology followed by
Mathlib's `MeasureTheory.Measure.isHaarMeasure_map`,
`MeasureTheory.Measure.isMulLeftInvariant_eq_smul`, and
`MeasureTheory.Measure.haarScalarFactor_pos_of_isHaarMeasure`.
For the last step, continuity on the second-countable target gives
almost-everywhere strong measurability; use `memLp_map_measure_iff` and
invariance under multiplication of the measure by a positive finite scalar.
The published `Langlands.haarMemLpInvariant` provides the corresponding
real-valued Haar-normalization comparison on one group. These are proof
dependencies and a proposed route, not hypotheses of these targets.

The existing `Langlands.QuotientIntegration` comparison for right-invariant
measures on a general left-coset space has a different domain and requires
subgroup averaging. Here the quotient is already a group and its actual
homomorphism is specified. The Haar pushforward theorem therefore applies
directly after properness is proved; no left/right quotient adapter is needed.

Specialization to a reductive rational-point group still requires its actual
topology, central subgroups, compactness and source-compatible Haar measures.
This generic analytic statement establishes none of those realizations and
does not discharge a Plancherel theorem.
