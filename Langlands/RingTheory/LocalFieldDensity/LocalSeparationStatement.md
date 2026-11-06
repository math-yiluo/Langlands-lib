# Separation in every evaluation neighbourhood of a smooth domain

Authors: Worker 135 and Worker 200.

`LocalSeparationStatement.{u,v}` is an unproved proposition definition. For
every complete nontrivially normed field `K`, smooth commutative `K`-algebra
`A` which is a domain, algebra point `x`, evaluation neighbourhood `U` of
`x`, and nonzero `a : A`, it asks for an actual algebra point `y ∈ U`
with `y a ≠ 0`. The field and algebra universes are independent. There
is no restriction on the characteristic and no topology on `A`.
`AlgPoint K A K` has precisely the published topology induced by all
coordinate evaluations into `K`.

This is an internal strengthening of the published global separation theorem
`exists_algHom_apply_ne_zero` in `LocalFieldDensity.Density`. The proposed
proof uses neighbourhood control in the inverse function theorem for a
finite submersive presentation, together with the existing algebraicity
argument over its free coordinates. This file supplies neither that proof
nor a chart as an assumption. It cites no external mathematical assertion.

The local requirement is needed to establish Zariski density of every
nonempty open subset of actual rational points in the dynamic open-cell
conullness proof. Global rational-point Zariski density alone does not give
this statement. Even after this statement is proved, the actual
scheme-point comparison, Haar-null closed-set theorem, and dynamic
open-cell complement comparison remain separate obligations. No Haar
measure, reductive group, integration formula or conullness conclusion
occurs in the proposition.
