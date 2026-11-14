# Fixed orbits from Lang's theorem on actual geometric group points

This internal specialization combines
[`exists_fixed_in_orbit_of_quotient_lang`](../../GroupTheory/LangFixedOrbit.md)
with the published Lang theorem
`Langlands.GroupScheme.exists_eq_inv_mul_descentBasePoint` in
[`Torus/FrobeniusConjugate`](../Torus/FrobeniusConjugate.md).
It uses that theorem on the actual rational points of a geometric base change.

Let `k` be a finite field, `Ω` an algebraically closed algebraic extension of
`k`, and `G` a smooth connected affine group scheme over `k`.
Let `H` act on `X`, and let `q` be a surjective homomorphism from `H` to
the `Ω`-rational points of `G_Ω`. Suppose that `θ : H → H` intertwines
`q` with the canonical Frobenius descent map on these points, and that
`τ (g • x) = θ g • τ x` for a map `τ : X → X`.
If the kernel of `q` fixes a supplied `x₀`, and `τ x₀ = h • x₀` for some
supplied `h : H`, then
`exists_fixed_in_orbit_of_finiteField_quotient` gives `g : H` such that
`τ (g • x₀) = g • x₀`.

The Lean proof supplies the quotient Lang equation with
`exists_eq_inv_mul_descentBasePoint`, reversing the equality in that theorem,
and applies the general orbit correction lemma.
`langSurjective_descentBasePoint` records this Lang surjectivity separately.
The canonical point map is
`descentBasePoint` for `FiniteField.frobeniusAlgEquivOfAlgebraic k Ω`.

The conclusion is conditional on the given action, reduction homomorphism,
surjectivity, equivariance, kernel action and orbit relation. In particular this
module does not construct a parahoric model or a chamber-to-Borel correspondence,
and does not prove the twisted-stable chamber statement.
