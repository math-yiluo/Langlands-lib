# Recovery of coefficient cocycles in a general field tower

This internal construction generalizes `GaloisCocycleFiniteRecovery` from an
intermediate-field carrier to an arbitrary field tower `k → E → K`. Its
provenance is that module's restriction and descent argument, the published
`GaloisPoint.restrictNormal_relativeAut` and relative extension comparisons,
and arbitrary Galois descent for affine coefficient points. It asserts no
original-literature theorem.

The fields have a common arbitrary universe. The algebras form a scalar tower,
`E/k` is normal, and `G` is a group scheme over `k`. Initially `c` takes values
in coefficient points over `K` and satisfies
`c (σ * τ) = c σ * conjugate σ (c τ)`. The required triviality premise is
`σ.restrictNormal E = 1 → c σ = 1`.

`value_eq_of_restrict_eq` proves that equal restrictions give equal values.
Indeed, `τ⁻¹ * σ` then restricts to one, and the cocycle formula for
`τ * (τ⁻¹ * σ)` gives the result. `conjugate_value` compares `τ * σ` with `σ`
when `τ` restricts to one. The cocycle formula and `c τ = 1` then show that
`τ` fixes `c σ` coefficientwise.

For the recovery constructions, additionally `K/k` is Galois and `G` is affine.
The relative extension `K/E` is Galois by the field-tower theorem.
`restrictNormal_relativeAut` identifies every relative automorphism as an
element of the restriction kernel. Thus `fixedValue` places each original
value in the actual relative fixed-point subgroup. `value` applies
`relativeAlgebraicDescend` to the value of a chosen normal lift of an
automorphism of `E/k`.

`extend_value` proves exact recovery for every automorphism of `K/k`, using
relative descent recovery and dependence only on restriction.
`value_mul` extends the claimed cocycle equation to `K`. Compatibility of
relative extension with conjugation and the original cocycle equation prove
the extended equation, and injectivity of relative extension proves the
equation over `E`. Neither finite degree nor an identification of `E` with a
specified intermediate-field subtype is needed.

The final section takes `c` in the rational points of the actual base change
of `G` to `K`. `baseChangeCoeffEquiv` transports its cocycle and kernel
triviality to coefficient points. `rationalValue` recovers coefficient values
over the supplied `E` and transports them back to rational points of the
actual base change. `relativeRationalExtend_rationalValue` recovers each
original value, and `rationalValue_mul` states the resulting rational cocycle
law with the actual `rationalConjugate` action. `exists_rational_cocycle`
packages these two properties.

This module does not construct a finite field, prove kernel triviality for an
arbitrary cocycle, recover an integral model, or establish any quotient,
residue, Frobenius or chamber conclusion.
