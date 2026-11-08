# Natural normalized compact comparison on the original target Levi

For the original intersection datum `D` and a simultaneous dynamic realization
`R`, `R.orbitProjectionKernelCompactIso` constructs a natural isomorphism from
`orbitProjectionKernelCoinvariantsFunctor` to `D.targetNormalizedCompactFunctor`.
The source ranges over every smooth complex representation of the original
source Levi, with group and coefficient universes independent. The target acts
on the original target Levi's own rational points.

The inducing subgroup is the full original orbit stabilizer
`Q ∩ z⁻¹ P z`. The component uses the same chosen `D.orbitCompactComparison R`
family on `compactSmoothStabilizerCoefficient A`, which bundles the existing
`stabilizerTwistedCoefficientFunctor.obj A` with its proved smoothness. It retains
the actual projection-kernel coinvariants and their maps.

`compactOrbitIntegralAbstractFamily` views that existing family as the generic
`SplitStagesComparisonFamily`, without choosing another integral or replacing
its coefficient representation. The helper proves normalization naturality at
this abstract group level before the represented source coefficients are
substituted. `compactInducedNaturalEquiv` then twists the integral component by
the original target inverse-half character, moves that character inside actual
compact induction, transports through the proved equality between the section
preimage and the literal target intersection copy, and postcomposes coefficient
values with `compactNormalizedCoefficientEquiv` restricted to that copy.

For each original smooth source morphism, the family property supplies the actual
kernel quotient map. `compactNormalizedCoefficientEquiv_natural` supplies the
actual original source Jacquet quotient map. The generic normalization theorem
combines them. A private proof-valued definition lets Lean infer this specialized
identity without manually retyping its large intermediate action expressions.
`orbitProjectionKernelCompactEquiv` restricts the resulting component through the
original Levi point equivalence. `NatIso.ofComponents` and the inferred identity
prove naturality on the entire original smooth source category.

This is an internal assembly of published comparisons. Its directly assembled
family component is used for the natural isomorphism; this file does not prove a
separate equality or standalone naturality theorem for the earlier
`compactInducedNormalizedEquiv` definition. The original stabilizer, smooth
coefficient, inverse-half normalization, subgroup equality and normalized
coefficient maps are retained.

The dynamic realization is still an explicit input. This intermediate does not
construct that realization, a relative-root presentation, character detection or
compactness of the actual target parabolic quotient. It also does not identify
the compact target with `D.pieceFunctor`, prove a represented pointwise evaluation
formula, or prove the closed `RepresentedGeometricLemmaOrbitComparisonStatement`.
