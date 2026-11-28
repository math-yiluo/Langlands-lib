# The character integral and the compressed coefficient trace

`CoefficientCharacterAveragingStatement` concerns `G = GL_n(F)` with `n > 0`
over a nonarchimedean local field. Let `Θ` be a character function of an
admissible representation `ρ`, and let `f(g) = conj ℓ(π(g)v)` be a conjugate
coefficient of a second representation. Let `H` be a compact open subgroup
fixing `v`. Suppose `Ψ` and `T` on the Borel quotient `G/Z` pull back to `Θ f`
and `ψ_H f` respectively, where `ψ_H` is `traceCoefficient ρ hρ.1 H`.
If `Ψ` is integrable for the given Haar measure `μ` on `G/Z`, the theorem
`integral_character_mul_star_coefficient_eq_integral_traceCoefficient` proves
that the two integrals for `μ` are equal. The field and both carriers have
independent universes.

This comparison gives the trace equality used in Clozel's character formula
for a conjugate coefficient. Its source is the distribution character
identity and right invariance of quotient Haar measure. The context is
Clozel, *Invariant harmonic analysis on the Schwartz space of a reductive
p-adic group* (1991), §3, formula (3.1) and its extension to a central
character on printed pp. 110–111 (PDF pp. 121–122). The quotient pullback
identities and absolute integrability of `Ψ` are hypotheses here.

For the proof, let `ε` be the indicator of `H` normalized to have integral one
for the auxiliary Haar measure `ν = RankinSelberg.generalLinearHaar F (n-1)`
on `G`. The integrated action of the left translate of `ε` by `g` is
`ρ(g)e_H`. The proof factors it through the finite-dimensional space `V^H`
and uses `FiniteRankEnd.trace_eq_of_factorization` to obtain `ψ_H(g)`.
The character identity for that test and left invariance of `ν` express
`ψ_H(g)` as `∫ ε(k) Θ(g k) dν(k)`.

On `H`, fixity of `v` gives `f(g k) = f(g)`. Outside `H`, `ε` vanishes.
The pointwise pullback identities therefore give
`T(q) = ∫ ε(k) Ψ(q ⋅ (k Z)) dν(k)` at every quotient point `q`.
The map `(k,q) ↦ (k,q ⋅ (k Z))` preserves `ν × μ` by right invariance of
`μ`. The proof uses `MeasurePreserving.skew_product` to transport
integrability of `(k,q) ↦ ε(k) Ψ(q)` along this map. Fubini and right
invariance reduce the integral of `T` to the integral of `Ψ` multiplied
by `∫ ε dν = 1`. The equality thus uses the given measure `μ` on both sides.
