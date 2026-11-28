# The character formula for a conjugate square-integrable coefficient of GL_n

Lean module: `Langlands.BaseChange.SquareIntegrableCoefficientCharacterFormulaStatement`. The
file states the proposition `SquareIntegrableCoefficientCharacterFormulaStatement.{u, uV}` and
does not prove it.

## The statement

Let `F : Type u` be a nonarchimedean local field of characteristic zero, `0 < n`,
`G = GL_n(F)`, `Z` its center and `G ⧸ Z` with its Borel σ-algebra
(`centralQuotientMeasurableSpace`). Let `ρ` on `V : Type uV` be an irreducible representation of
`G`, square-integrable modulo the center (`IsSquareIntegrable`). Then there is `Θ : G → ℂ` such
that

1. `Θ g` is the character value of `ρ` at every regular semisimple `g`
   (`HasCharacterValue ρ _ g (Θ g)`, with `IsRegularSemisimple g`: the characteristic
   polynomial of `g` is separable), and
2. for every Haar measure `μ` on `G ⧸ Z`, every irreducible representation `π` on
   `W : Type uV`, square-integrable modulo the center, every pair of unitary central characters
   `cρ`, `cπ` of `ρ` and `π` with the same underlying character, every vector `v : W` and
   every smooth functional `ℓ` of `π`, there is `Ψ : G ⧸ Z → ℂ` with
   `Ψ(gZ) = Θ(g) · conj ℓ(π(g) v)` for all `g`, `Ψ` is `μ`-integrable, and for every compact
   open subgroup `H` fixing `v` and every `T : G ⧸ Z → ℂ` with
   `T(gZ) = ψ^ρ_H(g) · conj ℓ(π(g) v)`,

   `∫_{G/Z} Ψ dμ = ∫_{G/Z} T dμ`.

Here `ψ^ρ_H = traceCoefficient ρ _ H` is the trace coefficient `g ↦ trace(e_H ρ(g) e_H)` on the
space of `H`-fixed vectors (module
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceCoefficientFamily`) and `conj` is
complex conjugation (`star`). The function `Θ` is chosen once for `ρ`, before `μ`, `π`, `v`
and `ℓ`; off the regular semisimple set its values are unconstrained by item 1, and they only
matter through the requirement that `Ψ` be well defined on `G ⧸ Z`.

## Source and derivation

Laurent Clozel, *Invariant harmonic analysis on the Schwartz space of a reductive p-adic
group*, in Barker and Sally (eds.), *Harmonic Analysis on Reductive Groups*, Progr. Math. 101,
Birkhäuser (1991), §3:

- Corollary 4, printed p. 108 (PDF p. 119): for tempered `π` and `f` in the Schwartz space
  `C(G)`, `trace π(f) = ∫_G Θ_π f`.
- Proof of Theorem 3, printed pp. 110–111 (PDF pp. 121–122), formula (3.1): for `f ∈ C(G/Z)`,
  `trace π₁(f) = ∫_{Z\G} Θ_{π₁}(x) f(x) dx`, the integral being absolutely convergent; for a
  non-trivial central character `ξ`, the same holds for `f ∈ C(G, ξ⁻¹)`.

The statement is (3.1) for `π₁ = ρ` and `f(g) = conj ℓ(π(g) v)`, together with Harish-Chandra's
theorem that the character of `ρ` is given on the regular semisimple set by a function
(item 1). This `f` is a `K`-finite matrix coefficient of the complex conjugate of `π`, which is
square-integrable modulo `Z` with central character inverse to that of `ρ`; such coefficients
lie in the Schwartz space `C(G, ξ⁻¹)` (Harish-Chandra). The integrand `Θ f` is invariant under
`Z` because the central characters have absolute value one and cancel, which is why `Ψ` is a
function on `G ⧸ Z`. The left side of (3.1) is rewritten through `H`-fixed vectors: since `v`
is `H`-fixed, `f` is right `H`-invariant, so `ρ(f) = ρ(f) e_H` has finite rank and

`trace ρ(f) = trace(e_H ρ(f) e_H |_{V^H}) = ∫_{G/Z} f(g) trace(e_H ρ(g) e_H |_{V^H}) dg
= ∫_{G/Z} ψ^ρ_H f`,

which is `∫ T dμ`. The non-regular elements form a null set, so `Ψ` and `Θ_ρ f` agree almost
everywhere, and absolute convergence in (3.1) is the integrability of `Ψ`. The measure `dx` on
`Z\G` in (3.1) is the same on both sides, so any Haar measure `μ` may be used.

The module `Langlands.BaseChange.EllipticCoefficientTraceReduction` uses this statement, with
`SquareIntegrableCoefficientNonellipticVanishingStatement` and the Schur orthogonality theorem
`exists_integral_traceCoefficient_mul_star_coefficient`, to derive
`EllipticCoefficientTraceStatement`.

Literature ID `provided-698170812a35ff43dbc4156af9f67a8384f95d97d5836529575e646643af617b`,
SHA-256 `c5cb36139e9cf3ed29fe1338a45488236cc69abdc4806d5ba2180456faba08ba`.
