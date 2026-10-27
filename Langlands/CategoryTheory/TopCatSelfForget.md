# The identity forgetful functor for continuous topological actions

`Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget` equips
`TopCat` with the identity functor as `HasForget₂ TopCat TopCat`. Its
compatibility equation is reflexivity. The declaration keeps its published
name and definition, extracted from
[NormContinuousAction](../Geometry/Analytic/NormContinuousAction.md) so that
continuous normal-level actions can reuse it without importing affinoid theory.

This is category-theoretic infrastructure for Mathlib's `ContAction`, with no
new mathematical assertion. It is not a global instance. Each consumer installs
it locally with `attribute [local instance]`.
