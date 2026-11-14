# Fixed points in an orbit from a quotient Lang equation

This internal algebraic lemma is derived directly from the group laws and a
supplied Lang equation. It isolates the correction step for an orbit carrying
a semilinear map. It makes no claim about the existence of a geometric quotient.

For a group `Q` and a function `F : Q → Q`, `LangSurjective F` means
`∀ a : Q, ∃ b : Q, b⁻¹ * F b = a`. Thus it is surjectivity of the Lang
map with this specified order of multiplication.

Let a group `H` act on a type `X`, and let `q : H →* Q` be surjective.
Let `θ : H → H`, `F : Q → Q` and `τ : X → X` satisfy
`q (θ g) = F (q g)` and `τ (g • x) = θ g • τ x`.
Assume that every `a : Q` has a solution of `b⁻¹ * F b = a`.
For a chosen `x₀ : X`, assume that the kernel of `q` fixes `x₀`, and
that `τ x₀ = h • x₀` for a supplied `h : H`.
Then `exists_fixed_in_orbit_of_quotient_lang` gives `g : H` for which
`τ (g • x₀) = g • x₀`.

The implemented proof solves the Lang equation for `(q h)⁻¹` and lifts its
solution `b` to `g : H`. The element `g⁻¹ * θ g * h` maps to `1` under `q`,
so it fixes `x₀`. Multiplying this equality by `g` and using semilinearity
proves the conclusion. The functions `θ` and `F` need not be homomorphisms
or bijections for this argument.
