# Transporting one metric and a whole semilinear action together

This internal transport argument was prepared by Worker 214 and adopted by
Worker 202 as a prerequisite for the proof of
`UnramifiedSemilinearMetricActionStatement`. It is an internal transport
argument using the published `integerValuationBuildingSameGroupComparison`
and Mathlib's induced metrics and permutation conjugation. It makes no new
claim about the construction of building geometry from the literature.

`Metric.KP.HasFiniteSemilinearMetricAction A Γ X τ` packages a complete NPC
metric on `X`, isometry of its existing `A`-action, and a homomorphism
`ρ : Γ →* Equiv.Perm X`. The homomorphism is semilinear for the specified
function `τ`, every `ρ σ` is an isometry for that same metric, and every
coefficient orbit is finite. The abstract statement only needs `Monoid Γ`
and the two supplied scalar actions; the properties of `τ` needed by
semilinearity are already asserted in the package.

`HasFiniteSemilinearMetricAction.transport` transfers this package through
one `A`-equivariant equivalence `e : X ≃ Y`. It induces the target metric
along `e.symm` and uses that isometry equivalence for completeness. It sends
each source NPC midpoint through `e`, so the midpoint inequality is
unchanged after applying `e.symm`. Inverse equivariance transfers isometry
of the existing scalar action.

The target coefficient homomorphism is the composition
`e.permCongrHom.toMonoidHom.comp ρ`. Its action at `y` is exactly
`e (ρ σ (e.symm y))`; hence both action laws follow from conjugating the
whole homomorphism. Semilinearity follows from inverse equivariance, source
semilinearity, and forward equivariance. The same induced metric makes
every conjugated permutation an isometry. Each target orbit is the image
under `e` of the source orbit at `e.symm y`, proving finiteness.

`unramifiedSemilinearMetricAction_iff_of_sameGroup` applies the abstract
transport argument to two supplied full-V6 data for the actual base change
of an `F`-group to `inertiaFixedField F`. The published comparison theorem
supplies an equivalence intertwining their identical rational-point
actions. The coefficient function is the actual `rationalConjugate`.

`unramifiedSemilinearMetricAction_of_oneDatum` reduces the exact published
every-datum statement to constructing one datum with the complete package
for each connected reductive group. The premise is a substantive remaining
construction: this fragment supplies no such datum, metric, coefficient
action, or finite-orbit proof. No special torus, stable apartment,
bounded-subgroup fixed point, or downstream special-torus result is used.
The final reduction is conditional on its displayed premise. The exact
`UnramifiedSemilinearMetricActionStatement` still requires constructing that
metric and action package independently.
