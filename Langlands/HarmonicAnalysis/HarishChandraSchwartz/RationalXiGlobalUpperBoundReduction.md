# From the actual chamber bound to the global Xi estimate

Worker 788, Task 7622. The theorem
`Langlands.HarishChandraSchwartz.rationalXiGlobalUpperBound_of_chamber_of_comparison`
proves the implication

```
RationalXiUpperBoundStatement →
RationalCartanIwasawaWeightComparisonStatement →
RationalXiGlobalUpperBoundStatement.
```

This is an internal derived assembly theorem. Both inputs are explicit
proposition hypotheses; this module proves neither input and supplies no
unconditional global estimate.

The proof extracts a finite family of centralizer factors from the supplied
Cartan covering. The simultaneous standard basis supplies a compatible
split component for the minimal Levi. The published chamber membership
lemma puts every dominant uniformizer power into its weak chamber.
Applying the two-sided chamber Xi bound and the published finite-translate
Cartan-cell lemma gives one constant `M` and one natural exponent `d`, uniform
in the cells. This works for the original compact Iwasawa subgroup `K` even
when it differs from the structural subgroup `K0`.

The published Cartan-cell height bound gives `σ(ϖ^y) ≤ σ(g) + B`.
Replacing `B` by `B' = max B 0` yields
`1 + σ(ϖ^y) ≤ (1 + B')(1 + σ(g))` and hence the corresponding inequality
of natural powers. The comparison hypothesis bounds the Iwasawa weight of
the representative by `Cw` times the weight of `g`. On the representative,
Iwasawa covariance identifies that weight with the square root of the
actual minimal-parabolic modulus. Multiplying these inequalities proves the
exact global conclusion with exponent `d` and positive constant
`max M 1 * Cw * (1 + B')^d`.

The target and its hypotheses are unchanged. The separate modulus comparison
is an outstanding prerequisite; the chamber estimate is the independent
representation-theoretic program of Task 5326. The proof reuses the published
`exists_mem_rationalCartanCell`, `exists_rationalXi_le_of_mem_rationalCartanCell`
and `exists_rationalHeight_uniformizerPowers_le` results rather than repeating
their arguments. The route is the Cartan/modulus argument explained in
Waldspurger's proof of II.4.4, with the finite-translate and arbitrary-height
adaptations made explicit here.
