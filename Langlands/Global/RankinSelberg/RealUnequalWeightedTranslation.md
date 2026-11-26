# Weighted real unequal reflection for fixed right translates

* `weighted_theta_of_growth`: let `W ∈ realUniformWhittakerModel r ds a` and
  `V ∈ realUniformWhittakerModel t es (-a)` satisfy
  `HasRealPairNormalizedGrowth ds es dds ees eb c hc sign` for `realUnequalIntegral h D W V` and
  `realUnequalDualIntegral h a D W V`. Then for every Gaussian rate `> 0`, shift and `β > 0` the
  theta identity of `realWeightedKernelReflection` holds for the two unequal-rank kernels, with
  Mellin variable `quotientDetAbs`. Convergence comes from `realUnequalPairConvergence` (with the
  regularity of the refined model), and Fubini identifies the dual integral with the integral of
  the dual kernel for the product measure.

* `RealUnequalWeightedTranslationStatement`: let `B`, `B'` be refined real Whittaker
  intertwiners (`IsRealUniformWhittakerIntertwiner`) for `a` and `-a`, and suppose the
  normalized growth holds for all pairs `B p`, `B' p'`. Then for fixed standard vectors `v`, `v'`,
  group elements `g`, `g'`, rate `> 0`, shift `C` and `β > 0`, with
  `f(x) = ordinaryWeight ds es eb c hc sign rate C (β x)` and
  `fd(x) = β · reflectedWeight dds ees rate C (β⁻¹ x)`, the weighted kernels
  `weightedOrdinary h (ρ g (B v)) (ρ g' (B' v')) f` and `weightedDual h (ρ g (B v)) (ρ g' (B' v')) fd`
  are integrable and have equal integrals.

`realUnequalWeightedTranslation` proves it: the weights are rapidly decreasing, so
`exists_compact_mellin_bounds` gives integrable bounds for the compact families of translates;
the theta identity of `weighted_theta_of_growth` on the pairs `B p`, `B' p'` is the hypothesis of
`realWhittakerTranslatedIntegrals`, which transports it to the fixed translates.

This is the real counterpart of the Library's `ComplexUnequalWeightedTranslation`. It is the
smaller-rank comparison of the larger-gap recurrence: in Jacquet, *Archimedean Rankin–Selberg
Integrals* (2009), §10.3, p. 75, the smaller-rank functional equation is applied to the `g`
integral of translated Whittaker functions in the passage from (10.7) to (10.8); the independent
weights used in the rigorous version of the argument are those of §10.4, p. 77.
