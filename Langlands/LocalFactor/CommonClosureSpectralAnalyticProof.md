# Analyticity of ordinary common-closure spectral local constants

Workers 1237 and 1749 prove
`Langlands.LocalFactor.commonClosureSpectralAnalytic`, whose type is exactly
`CommonClosureSpectralAnalyticStatement.{uF,uV}`. The field universe `uF`
and representation-carrier parameter `uV` stay independent, with the
published carrier convention `max uF uV`.

For every prime, finite p-adic field `F`, reciprocity family `e`, assignment
`ε` and supplied proof `hε : NonabelianSystem.IsSystem F e ε`, the theorem
gives complex analyticity at every point for

```
z ↦ (conditionalDeligneValue F e ε hε E ψ μ x z : ℂ).
```

Here `E` is any finite intermediate field in the specified algebraic
closure, `ψ` and `μ` are any supplied additive character and Haar measure,
and `x` is any class in the existing continuous exact virtual group
`Virtual F E`. This is the original value
`ε E ψ μ (virtualTwist F E z x)`, using the actual subgroup action,
restricted base degree and residue cardinality, and the canonical local
topology on each intermediate field. The theorem retains precisely the
hypotheses of the named statement.

This module is an internal assembly of three proved Library components.
The statement module documents the original-source correspondence with
Tate's ordinary spectral epsilon formula. The present proof uses the
published rank-one calculation and exact degree-zero generation directly.

`rankOneAnalytic hε` packages
`CommonClosureSpectralAnalytic.weilCharacter_analyticAt` from
`CommonClosureRankOneSpectral` as `RankOneAnalytic ε`. That theorem proves
the actual supplied-system value on each continuous character class is
analytic. Its norm-character comparison uses the normalized reciprocity
already contained in `hε`; its exponential formula comes from the two
branches of the existing abelian epsilon expression.

`spectralAnalytic_of_generation` applies
`CommonClosureSpectralAnalytic.analyticAt_of_generation` from
`CommonClosureSpectralGenerationReduction` separately at every prime and
base field. The reduction proves that the classes with analytic spectral
value form an additive subgroup: exact sums give products and negatives
give inverses, and values are nonzero because they lie in `ℂˣ`. Spectral
twisting commutes with actual induction. The system's degree-zero
induction relation therefore makes each induced character difference
analytic. Generation puts every degree-zero class in this subgroup, and
the trivial character class supplies the remaining integer degree.

The final theorem applies this reduction to the proved
`Langlands.LocalFactor.commonClosureDegreeZeroGeneration` from
`CommonClosureGenerationProof`, at the same independent universes. That
result supplies generation for the actual common-closure groups and exact
induction maps, including the required finite-quotient and intermediate-field
comparisons. Generation and rank-one analyticity are thus discharged in
the final theorem; neither remains an additional hypothesis.

The result concerns any supplied system satisfying the published system
laws. It proves the full ordinary spectral analyticity statement without
constructing a system or asserting the local Langlands correspondence or
Henniart's induction conclusion.
