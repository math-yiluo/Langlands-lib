# Actual normalized induction transport

This internal module derives the induction transport needed by the actual
parabolic-orbit Jacquet comparison from the published normalized coefficient
equivalence, character-twist transport, smooth-induction transport, and
compactness of the actual refined parabolic quotient. It adds no measure,
comparison, or character-cancellation hypothesis.

The general helpers have the following meanings. `smoothPullbackFunctor` pulls
a smooth action back along a continuous homomorphism and retains each original
linear map. `subgroupEqualityFunctor_eq_pullback` identifies equality relabeling
with pullback along the actual subgroup equivalence, by equality elimination.
`compactInducedSubgroupCongr` and `smoothInducedSubgroupCongr` relabel the inducing
subgroup along equality and preserve the ambient functions; their evaluation
formulas express this preservation. `compactSmoothEquiv` is the canonical
compact-induction inclusion, made invertible when the actual coset space is
compact. Its forward evaluation is unchanged.

`parabolicOrbitIntegratedCoefficient` is the genuine nested section action,
twisted by the complex embedding of the actual quotient-integration Haar ratio.
Its source inducing coefficient already contains the positive coarse source
half modulus. `parabolicOrbitIntegratedCoefficientMap` uses the canonical nested
coinvariant map for every original source intertwiner. The scalar twist retains
that map's underlying linear map. These definitions do not assert existence of
an integral comparison.

For every prime, actual finite p-adic extension `F`, supplied compatible
`TopologicalData T`, block shapes `B,C`, minimal representative `w`, and supplied
refinements `S,R` with both full `IsIntersectionRefinement` hypotheses,
`parabolicOrbitInductionTransportEquiv` identifies

```
twist inverseTargetHalf (compactInduced K integratedCoefficient)
```

with the actual normalized refined induction of normalized source refined
Jacquet, transported by inverse intersection conjugation. Here `K` is the actual
stages quotient subgroup. The proof first uses `compactInductionTwistEquiv` to
move the inverse target half into the inducing coefficient. The supplied p-adic
topology makes `K`'s actual coset space compact: the proved equality of `K` with
the supplied target refined parabolic reduces this to
`refinedParabolicQuotientCompact`. Thus `compactSmoothEquiv` applies. Next,
`smoothInducedEquiv` applies the published
`parabolicOrbitNormalizedNestedCoefficientEquiv`, which has already proved all
normalizing-character cancellation. Finally, `smoothInducedSubgroupCongr`
relabels `K` as that refined parabolic. No residual character remains.

If `eρ` denotes the normalized coefficient equivalence, evaluation of the
resulting transport at an actual target Levi element `x` is

```
eρ ((inverseTargetHalf x : ℂ) • f(x)).
```

The evaluation theorem follows from subgroup relabeling and the explicit
underlying induction maps. Naturality for every original source intertwiner
follows pointwise from this formula, linearity in the displayed scalar, and
`parabolicOrbitNormalizedNestedCoefficientEquiv_natural`. The induced source map
is canonical postcomposition by `parabolicOrbitIntegratedCoefficientMap`;
applying the common inverse-half twist keeps its linear map. The target map is
exactly `normalizedRefinedInducedMap` of `refinedIntersectionTransportMap` of
`normalizedRefinedJacquetMap`. Coefficient modules and intertwining maps may
have independent universes, without dimension or admissibility restrictions.

`geometricPieceFunctor_eq_pullback` additionally rewrites the literal published
geometric-piece functor using continuous pullbacks along the supplied subgroup
identifications. Its proof applies the general equality-relabeling identity to
the two equality functors. The intermediate inverse-conjugation transport and
the actual normalized Jacquet and induction functors are the published ones.

These are internal consequences of the imported constructions, rather than a
transcription of a new external theorem. The module supplies induction
transport and its naturality; the integral comparison and final natural
isomorphism of the host orbit functors are separate results.
