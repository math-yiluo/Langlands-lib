# Depth-zero opposite factors from actual root models

Author: Worker 200.

Lean module:
`Langlands.Geometry.Building.UnramifiedFixedDepthZeroOppositeModelReduction`.

This module states and proves an internal conditional reduction:

```
UnramifiedFixedRootModelStatement.{u} →
  IntegralOppositeFactorsStatement.{u} →
    UnramifiedFixedDepthZeroOppositeStatement.{u}.
```

The proposition is
`UnramifiedFixedDepthZeroOppositeModelReductionStatement`; its proof is
`unramifiedFixedDepthZeroOpposite_of_rootModels_of_integralOpposite`.
The conclusion is exactly the published target, at arbitrary universe `u`.
Both antecedents remain explicit premises; neither is proved by this reduction.
This module therefore supplies no unconditional proof of the depth-zero target.

## Implemented proof

Fix all the data of the target and a Galois-fixed point `z`. Apply the model
statement to obtain actual `D₀`, `T₀` and `Q₀`, together with the two root-point
comparisons. For the prescribed `g ∈ U_a(F)` with restricted value zero, the
nonnegative comparison shows `g ∈ D₀.neutral.integralPoints`. The strict
comparison shows `g ∉ Q₀.positivePoints`, since otherwise its value would be
strictly positive.

Apply the integral opposite-factor statement to this same model, torus and
quotient and to the factors `g'`, `g''` already supplied by the target. Its
right-to-left implication gives that both factors belong to the neutral
integral-point image. The published theorem `relativeRootNegation` proves that
`-a` is an actual relative root. The nonnegative model comparison at that root
then gives `0 ≤ φ z (-a) g'` and `0 ≤ φ z (-a) g''`.

No uniqueness or construction of the factors is used: the model statement
quantifies over all root points, and the opposite-factor statement quantifies
over all factors satisfying the normalizer condition. The argument applies to
multipliable roots as well. It retains the target's nonidentity condition on
`g` and does not add a nonidentity condition on either opposite factor.

## Provenance and remaining obligations

This is an internal composition of the two stated prerequisite interfaces and
the published actual-relative-root negation theorem. It formalizes the final
application of the integral opposite-factor criterion in the proof of
Kaletha–Prasad Proposition 9.4.9. The paired Markdown of each prerequisite
describes its source correspondence and construction obligations. No additional
literature assertion is used in this composition.

A proof of `UnramifiedFixedRootModelStatement` must construct the actual models
and prove both comparisons for the supplied apartment data. A proof of
`IntegralOppositeFactorsStatement` must establish the integral opposite-factor
criterion for all its supplied models. These substantial prerequisites must be
proved before this reduction can give the exact target without assumptions.
