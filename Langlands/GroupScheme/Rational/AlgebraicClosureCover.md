# Algebraic-closure covers of field-valued tests

This module contains the existing
`Langlands.GroupScheme.QuasiSplitRegularConjugate.algebraicClosureCoverPoint`
construction extracted from
[QuasiSplitRegularConjugateReduction](QuasiSplitRegularConjugateReduction.md).
Its public name, type and implementation are unchanged.

For fields `K` and `L` with a `K`-algebra structure on `L`, it constructs
`Spec (AlgebraicClosure L) → Spec L` as a morphism over `Spec K`. The underlying
scheme map is induced by the inclusion of `L` into its algebraic closure,
and the over-category condition is the scalar-tower identity.

The rational-conjugacy reduction and the
[strongly regular fibre transport](ClassFunctionsStronglyRegularFibresTransport.md)
share this construction. This extraction introduces no new mathematical result.
