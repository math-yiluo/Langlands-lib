# The two-cocycle obstruction for a central lift

Let `Γ` act by automorphisms on the groups in a central sequence
`A → B → C` with abelian kernel `A`. For a crossed cocycle `c` in `C`,
`CentralCocycleLift` records a lift `b(σ)` of each `c(σ)` and an
`A`-valued multiplication defect `d(σ,τ)`. The identity defining the
defect is `i(d(σ,τ)) b(στ) = b(σ) σ(b(τ))`, where `i` is the map to
`B`. Exactness at `B` produces such defects from coefficient lifts.

If `i` is injective, equivariant and central, the defect is a
multiplicative two-cocycle with Mathlib's inhomogeneous convention.
The proof compares the two associations of the product of three
lifted coefficients. If `a` has two-coboundary `d`, the new coefficient
`i(a(σ))⁻¹ b(σ)` is a crossed cocycle, with the same image in `C`.
Conversely, an existing crossed-cocycle lift gives a primitive by
lifting the pointwise ratio between the original and crossed lifts
back to `A` and applying injectivity of `i`.

These internal identities provide the algebraic part of a central
obstruction argument. The construction takes coefficient lifts as
inputs and works with the specified group actions.
