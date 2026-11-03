# Canonical norm depth and conductor: proof

Authors: Worker 84 (proof and original Markdown) and Worker 723 (submission
and Markdown revision), for task `cf12dc99-8684-4d66-bb49-c12c7f3ec32b`,
revision 1. This file describes the submitted proof contribution; it
becomes an accepted result only after independent review and publication.

The module `Langlands.HarmonicAnalysis.CanonicalConductorDepthProof` proves
`Langlands.HarmonicAnalysis.canonicalConductorDepth.{u}` with exact type
`Langlands.HarmonicAnalysis.CanonicalConductorDepthStatement.{u}`, the
conjunction of `CanonicalPrincipalUnitDepthStatement.{u}` and
`CanonicalCharacterDepthStatement.{u}`. The statement pair and its imports
are used unchanged. The proof covers every prime `p`, including two, every
`F : PadicField.{u} p` in the arbitrary carrier universe `u`, every supplied
`T : F.TopologicalData`, and every predicate `P`. It adds no hypothesis.

## A field neighborhood inside each principal-unit level

The private helper `principalUnitNeighborhood` fixes a level `n` and
works in the topology `T.topology`, with the valuative relation and local
field structure of `T`. It intersects three sets:

- the integer ring `T.Integers`, open by Mathlib's
  `Valuation.isOpen_integer`;
- the preimage of `T.Integers` under inversion, a neighborhood of one by
  `continuousAt_inv₀`;
- the preimage of `T.Integers` under `x ↦ (x - 1) / T.uniformizer ^ n`, a
  neighborhood of one because this map is continuous at one and sends one
  to zero.

Let a unit `x` lie in the intersection. The published
`mem_integers_iff_discreteValuation_le_one` turns the first two conditions
into `T.discreteValuation x ≤ 1` and `T.discreteValuation x⁻¹ ≤ 1`. Since
the valuation of a unit is positive, these give
`T.discreteValuation x = 1`. With the third condition, the published
`mem_principalUnits_iff_div_mem_integers` gives `x ∈ T.principalUnits n`.
Level zero is included.

## Canonical balls inside principal-unit levels

The private `canonicalPrincipalUnitDepth` proves the first conjunct. The
published `T.topology_eq_canonicalNormTopology` (from
`Langlands.LocalField.Normalization.Proof`) rewrites the neighborhood above
into a neighborhood of one in the metric topology of
`F.canonicalNormedField`. `Metric.mem_nhds_iff` then supplies a radius
`ε > 0` whose open ball about one lies inside it. Since `1 < p`, Mathlib's
`exists_pow_lt_of_lt_one` gives `k` with `(p⁻¹)^k < ε`, and `k` is the
required `s`: if `F.canonicalNorm (x - 1) < p^(-k)`, then `x` lies in the
ball and hence in `T.principalUnits n`. The radius depends only on `p`,
`F`, `T` and `n`, not on any character.

The proof compares neighborhood systems only. It uses no equality between
`F.canonicalNorm` and the residue-normalized absolute value of `T`, and no
explicit formula for `s`.

## Equivalence for an arbitrary character predicate

The private `canonicalBall_mem_nhds` shows that, for each `s`, the set of
units `x` with `F.canonicalNorm (x - 1) < p^(-s)` is a neighborhood of one in
`F.Carrierˣ` with the topology from `T`. After the same topology rewrite,
the set is open, being a strict sublevel set of the continuous map
`x ↦ ‖(x : F.Carrier) - 1‖`. It contains one because `p^(-s) > 0`.

The private `canonicalCharacterDepth` proves the second conjunct from the
first one. Fix `P`.

- From depth to conductor: given a threshold `r`, take the radius `s` for
  level `r` from the first conjunct. The hypothesis supplies `χ` with `P χ`
  and a unit `x` with `F.canonicalNorm (x - 1) < p^(-s)` and `χ x ≠ 1`, so
  `x ∈ T.principalUnits r`. If `T.multiplicativeConductor χ ≤ r`, the
  published `multiplicativeTrivialAt_iff_conductor_le` makes `χ` trivial on
  `T.principalUnits r`, a contradiction. Hence `r < T.multiplicativeConductor χ`,
  in particular `r ≤ T.multiplicativeConductor χ`.
- From conductor to depth: given `s`, the published
  `exists_principalUnits_subset` (cofinality of principal units among
  neighborhoods of one) supplies `n` with `T.principalUnits n` inside the
  canonical ball of radius `p^(-s)`. The hypothesis at threshold `n + 1`
  supplies `χ` with `P χ` and `n + 1 ≤ T.multiplicativeConductor χ`. The
  published `exists_nontrivial_below_multiplicativeConductor` gives
  `x ∈ T.principalUnits n` with `χ x ≠ 1`, and this `x` lies in the ball.

In both directions the witness character is the one supplied by the
hypothesis, so `P` is retained on it. All characters are continuous for the
topology given by `T`.

The theorem `canonicalConductorDepth` pairs the two conjuncts. All helpers
are private, so this is the only public declaration of the module.

## Dependencies and checks

The module imports the target statement module, which imports
`Langlands.HarmonicAnalysis.Conductor`. That module supplies the principal-unit
filtration, the multiplicative conductor and the five published lemmas
used above. The proof module also imports
`Langlands.LocalField.Normalization.Proof`, for the topology comparison, and
`Mathlib.Analysis.SpecificLimits.Basic`, for geometric decay.

A development `lean_check` (diagnostic
`32a3c78c-6662-493a-b54e-57a35bfa837c`, Library base
`5d3754ec863f6d5013aca65cbcec0801e6972d1f`) built the module by Lake with
zero errors and zero warnings. It reported only the axioms `propext`,
`Classical.choice` and `Quot.sound` for `canonicalConductorDepth`. This
check is development evidence. It is not exact-target validation or
independent review.

## Provenance and scope

This is a derived Library adapter, not a transcription of a theorem in the
literature. Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p* (1998), states Lemma 4.7 on printed p.201 (PDF p.25): there are
characters in general position of arbitrarily large conductor. Its proof on
printed pp.204–206 (PDF pp.28–30), especially p.205, keeps the stabilizer
condition (4.12) while making the conductor large. The registered source
`harris-1998-local-langlands` has SHA-256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`. The
statement pair documents why the Library needs this comparison: the
auxiliary-character interface is phrased in canonical norm balls, while the
Library conductor uses the principal-unit filtration of `T`.

The proof asserts no existence of a character, no exact stabilizer
condition, no reciprocity transport to the Weil group, and no repair of
Harris's characteristic-two construction.
