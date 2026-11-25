# Covariance of the twisting operator with right translation

Module `Langlands.TraceFormula.IsotypicTrace.TwistCovariance`. Internal to the reduction of
`GroupSchemeCuspidalIsotypicTraceFactorizationStatement` to one local occurrence.

`twistOperator_quotientL2RightTranslate`: let `Θ` be a topological automorphism of `G(𝔸_F)`
preserving the positive rational subgroup `Γ`, with the inverse induced map on `Γ \ G(𝔸_F)`
measure preserving. For every right-invariant quotient measure and `φ` in the quotient `L²`
space,

`I_Θ (R(a) φ) = R(Θ a) (I_Θ φ)`,

where `I_Θ = twistOperator` (`φ ↦ φ ∘ Θ̄⁻¹`) and `R(a) = quotientL2RightTranslate` (right
translation by `a`). Both sides are `Lp.compMeasurePreserving` along a composite map. By
`Lp.compMeasurePreserving_comp_apply` the claim reduces to equality of the two maps on the
quotient. Both send `Γx` to `Γ Θ⁻¹(x) a`, because `Θ⁻¹(x Θ(a)) = Θ⁻¹(x) a`. This is the
relation `I_Θ R(a) = R(Θ a) I_Θ` used for the covariance in the twisted clause of
`CuspidalOccurrenceReduction`.
