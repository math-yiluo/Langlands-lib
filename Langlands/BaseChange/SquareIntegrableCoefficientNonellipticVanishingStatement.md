# The non-elliptic part of a class function times a square-integrable coefficient

Lean module: `Langlands.BaseChange.SquareIntegrableCoefficientNonellipticVanishingStatement`.
The file states the proposition `SquareIntegrableCoefficientNonellipticVanishingStatement.{u, uV}`
and does not prove it.

## The statement

Let `F : Type u` be a nonarchimedean local field of characteristic zero, `0 < n`,
`G = GL_n(F)`, `Z` its center and `G ⧸ Z` with its Borel σ-algebra
(`centralQuotientMeasurableSpace`). Take

- a Haar measure `μ` on `G ⧸ Z`;
- an irreducible representation `π` on `W : Type uV`, square-integrable modulo the center
  (`IsSquareIntegrable`);
- a function `Θ : G → ℂ` invariant under conjugation at regular semisimple elements:
  `Θ(a⁻¹ g a) = Θ(g)` whenever `g` is regular semisimple (`IsRegularSemisimple`: separable
  characteristic polynomial);
- a vector `v : W` and a smooth functional `ℓ` of `π`;
- a `μ`-integrable `Ψ : G ⧸ Z → ℂ` with `Ψ(gZ) = Θ(g) · conj ℓ(π(g) v)` for all `g`.

Then there is `Φ : G ⧸ Z → ℂ` with

`Φ(gZ) = 0` if `g` is regular elliptic, `Φ(gZ) = Θ(g) · conj ℓ(π(g) v)` otherwise,

and `Φ` is `μ`-integrable with `∫_{G/Z} Φ dμ = 0`. Here `IsRegularElliptic g` means that the
characteristic polynomial of `g` is separable and irreducible, and `conj` is complex conjugation
(`star`). No relation between `Θ` and `π` is assumed beyond the integrability of `Ψ`.

The hypothesis `0 < n` is needed: for `n = 0` the group is trivial, its one element is not
regular elliptic (the characteristic polynomial `1` is a unit, hence not irreducible), and
`∫ Φ dμ = Θ(1) conj ℓ(v) μ(G ⧸ Z)` need not vanish.

## Source and derivation

Laurent Clozel, *Invariant harmonic analysis on the Schwartz space of a reductive p-adic
group*, in Barker and Sally (eds.), *Harmonic Analysis on Reductive Groups*, Progr. Math. 101,
Birkhäuser (1991), §3:

- Proposition 5 (i), printed p. 108 (PDF p. 119), the "Selberg principle": if `π` is
  square-integrable modulo `Z`, `f` is a `K`-finite matrix coefficient of `π` and `γ` is a
  regular element of a non-elliptic Cartan subgroup `T`, then `∫_{T\G} f(g⁻¹ γ g) dg/dt = 0`.
  Its proof (printed p. 109, PDF p. 120) uses that the constant terms of `f` along proper
  parabolic subgroups vanish.
- Proof of Theorem 3, printed p. 110 (PDF p. 121): the absolutely convergent integral (3.1) is
  rewritten with the Weyl integration formula, and Proposition 5 removes the non-elliptic
  Cartan subgroups.

The statement is this step for an arbitrary class function `Θ`. The function
`f(g) = conj ℓ(π(g) v)` is a `K`-finite matrix coefficient of the complex conjugate of `π`,
which is again square-integrable modulo `Z`. The non-regular elements form a null set, and the
regular elliptic set is open, so `Φ` is `Ψ` times the indicator of a measurable set and is
integrable. By the Weyl integration formula on `G ⧸ Z`, `∫ Φ` is a finite sum over the
conjugacy classes of non-elliptic Cartan subgroups `T` of

`|W(G, T)|⁻¹ ∫_{T/Z} |D(t)| Θ(t) (∫_{G/T} f(g t g⁻¹) dġ) dt`,

using `Θ(g t g⁻¹) = Θ(t)` at regular `t`. The same formula applied to `|Ψ|` shows that the
iterated integrals converge absolutely, so Fubini's theorem applies, and the inner orbital
integrals vanish for every regular `t ∈ T` by Proposition 5 (i).

The module `Langlands.BaseChange.EllipticCoefficientTraceReduction` uses this statement, with
`SquareIntegrableCoefficientCharacterFormulaStatement` and the Schur orthogonality theorem
`exists_integral_traceCoefficient_mul_star_coefficient`, to derive
`EllipticCoefficientTraceStatement`.

Literature ID `provided-698170812a35ff43dbc4156af9f67a8384f95d97d5836529575e646643af617b`,
SHA-256 `c5cb36139e9cf3ed29fe1338a45488236cc69abdc4806d5ba2180456faba08ba`.
