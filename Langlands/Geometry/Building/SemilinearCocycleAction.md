# Twisting a semilinear permutation action by a cocycle

This internal algebraic module constructs the permutation action
`SemilinearCocycleAction.action` on an existing `H`-set `X`. Its inputs are a group
homomorphism `ρ : Γ → MulAut H`, a permutation action `A` of `Γ` on `X` satisfying
`A σ (g • x) = ρ σ g • A σ x`, and a crossed homomorphism
`c (σ * τ) = c σ * ρ σ (c τ)`. The resulting permutation sends `x` to
`c σ • A σ x`. The cocycle law proves its multiplication law and, with the inverse
index, both inverse identities.

For `Γ = Aut(K/k)`, `finite_range_of_finite_fixing_field` proves that `c` has finite
range if it is trivial on the pointwise fixing subgroup of a finite-dimensional
intermediate field `E`. Restricting automorphisms to `E` gives a map into the finite
type `E →ₐ[k] K`. If two restrictions agree, their quotient fixes `E`, so the
cocycle law gives equal values of `c`. Choosing representatives of the restriction
image bounds the range of `c` by a finite set. This argument needs neither
normality nor separability of `E`.

Finally, `finite_orbit_of_fixed` bounds the twisted orbit of an `A`-fixed point by
the image of the finite range of `c` under `g ↦ g • x`.

The content is derived directly from group laws, semilinearity, and Mathlib's
finiteness of algebra embeddings of a finite-dimensional field extension. It is
an implementation prerequisite for twisted actions on the maximal unramified
building; it does not supply a metric, a common fixed point, or a stable chamber.
