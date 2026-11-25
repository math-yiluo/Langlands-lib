# Proof of the all-parameter spherical functional equation

This module proves the published statement
`Langlands.Conductor.SphericalLaurentFunctionalEquationStatement.{uF, uV}` (module
`SphericalLaurentFunctionalEquationStatement`) with no hypotheses:

`theorem sphericalLaurentFunctionalEquation : SphericalLaurentFunctionalEquationStatement.{uF, uV}`

Let `F` be a nonarchimedean local field with Jacquet's normalizations, `ν` a Haar
measure on `F` self-dual for `ψ`, `π` a generic representation of `GL_(n+2)(F)` with
standard L-polynomial `P` and epsilon factor `c q^(-ms)` against the trivial character,
and `ℓ` a nonzero `ψ`-Whittaker functional. The statement gives a polynomial `Pdual`
with constant term `1` such that, for every vector `v` of the Whittaker model of `ℓ` and
every Satake parameter `x : Fin (n + 1) → ℂˣ`, unitary or not:

- the corank-one integral `Ψ(s, v, W(x; ψ̄))` and its dual integral converge on right
  half-planes;
- the first integral continues to `Q · ∏ i, P(x_i X)⁻¹`, `X = q^(-s)`, for a Laurent
  polynomial `Q`, and the dual integral continues to a rational function `Rdual`;
- the two continuations satisfy `NormalizedFunctionalEquation` with the polynomials
  `∏ P(x_i X)` and `∏ Pdual(x_i⁻¹ X)`, root of unity `1`, constant
  `c^(n+1) (∏ x_i)^m`, exponent `n + 1` and degree `(n + 1) m`.

The statement exposes only these properties. Internally, the proof takes `Pdual` to be
the standard L-polynomial of the inverse-transpose pullback `π̃` of `π`, and `Rdual` to
be `Qd · ∏ i, Pdual(x_i⁻¹ X)⁻¹` for a Laurent polynomial `Qd`.

## Proof

The proof is a single application of the reduction
`sphericalLaurentFunctionalEquation_of_corankOne_of_laurent` (module
`SphericalLaurentFunctionalEquationReduction`) to two theorems proved in the Library:

1. `sphericalCorankOneFunctionalEquation : SphericalCorankOneFunctionalEquationStatement`
   (module `SphericalCorankOneFunctionalEquationProof`). This is the
   functional equation for unitary Satake parameters, `‖x_i‖ = 1`.
2. `sphericalCorankOneLaurent : SphericalCorankOneLaurentStatement` (module
   `SphericalCorankOneLaurentProof`). It gives the standard L-polynomial, convergence on a
   right half-plane, and the Laurent numerator
   `Ψ(s, w, W(x; ψ̄)) ∏ P(x_i q^(-s)) = q^(-Ns) Q(q^(-s))`, for every vector `w` and
   every parameter `x`. These are the first three conjuncts of
   `SphericalLFactorGenerationStatement`. The fourth conjunct, the generation clause
   (Jacquet's Lemma 4), is not needed.

The reduction applies the second theorem to `π` and to its inverse-transpose pullback
`π̃`, and so obtains `Pdual`, the convergence of both integrals and Laurent continuations
for every `x`. It rewrites the dual integral as a corank-one integral of `π̃` against
`W(x⁻¹; ψ)`. The first theorem gives the functional equation at unitary `x`, and
`normalizedFunctionalEquation_of_unitary` (module `SphericalUnitaryExtension`) extends it
to every `x`. The Markdown of the reduction module describes these steps.

The universe parameters `uF` (of `F`) and `uV` (of the representation space) are passed
through unchanged. Both input theorems are stated for arbitrary independent universes
`uF` and `uV`.

## Provenance

Internal. This module only combines Library results. The underlying mathematics is JPSS
1981, (4.2)(3), and JPSS 1983, Theorems (2.7) and (3.1). These are formalized in the two
input theorems, and the extension to all parameters is in the reduction module.
