# Elliptic orbital integrals of square-integrable coefficients of GL_n

Lean module: `Langlands.BaseChange.EllipticOrbitalCoefficientStatement`. The file states the
proposition `EllipticOrbitalCoefficientStatement.{u, uV}` and does not prove it.

## The statement

Let `F : Type u` be a nonarchimedean local field of characteristic zero, `0 < n`,
`G = GL_n(F)`, `Z` its center, and give `G ⧸ Z` its Borel σ-algebra
(`centralQuotientMeasurableSpace`). For

- every Haar measure `μ` on `G ⧸ Z`,
- every representation `π` of `G` on a complex vector space `W : Type uV` with
  `IsSquareIntegrable π` (admissible, unitary central character, coefficients square-integrable
  on `G ⧸ Z`) and `π.IsIrreducible`,
- every `d` with `IsCentralFormalDegree μ π d` (the formal degree of `π` for `μ`, module
  `Langlands.BaseChange.CentralQuotientFormalDegree`),
- every regular elliptic `γ` (characteristic polynomial separable and irreducible) and every `c`
  with `HasCharacterValue π _ γ c` (the character of `π` is the constant `c` near `γ`),
- every vector `v : W` and smooth functional `ℓ`,

there is a function `o` on `G ⧸ Z` with `o(gZ) = ℓ(π(g γ g⁻¹) v)`, `o` is `μ`-integrable, and

`∫_{G/Z} o dμ = d⁻¹ ℓ(v) c`.

The value `ℓ(π(g γ g⁻¹) v)` only depends on `gZ`, since central elements commute with `γ`.
Integrability of `o` is the absolute convergence of the orbital integral.

## Source

Laurent Clozel, *Invariant harmonic analysis on the Schwartz space of a reductive p-adic
group*, in Barker and Sally (eds.), *Harmonic Analysis on Reductive Groups*, Progr. Math. 101,
Birkhäuser (1991), §3, Proposition 5 (ii), printed p. 108 (PDF p. 119), with the proof on
printed pp. 109–110 (PDF pp. 120–121). For a square-integrable `π`, a `K`-finite matrix
coefficient `f` of `π` and a regular `γ` in an elliptic Cartan subgroup `T`:

`∫_{T\G} f(g⁻¹ γ g) dg/dt = d(π)⁻¹ f(1) Θ_π(γ)`,

where the measure on `Z\G` computes the formal degree and `Z\T` has volume `1`.

Correspondence:

- `G = GL_n(F)`, a connected reductive group over a `p`-adic field. Clozel's `K`-finite
  coefficients of an admissible `π` are the functions `g ↦ ℓ(π(g) v)` with `v` a vector and
  `ℓ` a smooth functional; here `f(1) = ℓ(v)`.
- The function `g ↦ f(g⁻¹ γ g)` is left `T`-invariant: for `t ∈ T`,
  `f((tg)⁻¹ γ (tg)) = f(g⁻¹ t⁻¹ γ t g) = f(g⁻¹ γ g)` because `t` commutes with `γ`. So it
  descends to `T\G`, which is how Clozel's integral is formed. Disintegrating the Haar measure
  `dg` of `Z\G` along the left `Z\T`-orbits, with the Haar probability measure `dt` on the
  compact group `Z\T`, gives
  `∫_{Z\G} f(g⁻¹ γ g) dg = ∫_{T\G} ∫_{Z\T} f((tg)⁻¹ γ (tg)) dt (dg/dt) = ∫_{T\G} f(g⁻¹ γ g) dg/dt`.
  Thus Clozel's left side is the integral over `Z\G`, which is `G ⧸ Z` since `Z` is central.
  The substitution `g ↦ g⁻¹` of the integration variable (Haar measures on `G ⧸ Z` are
  inversion invariant, see `centralQuotient_isInvInvariant`) turns `f(g⁻¹ γ g)` into
  `f(g γ g⁻¹)`, the integrand of the Lean statement.
- `Θ_π(γ)` is the value of the character function at the regular elliptic `γ`, which is the
  Library's `HasCharacterValue` (the distribution character equals `c` times Haar measure on
  test functions supported near `γ`).
- `d(π)` is the formal degree for the measure on `Z\G`, which is `IsCentralFormalDegree`.

Clozel's proof uses Lemma 2 (printed p. 109), a consequence of the Schur orthogonality
relations, the absolute convergence of the elliptic orbital integrals of a Schwartz function
and their local constancy near `γ`.

Literature ID `provided-698170812a35ff43dbc4156af9f67a8384f95d97d5836529575e646643af617b`,
SHA-256 `c5cb36139e9cf3ed29fe1338a45488236cc69abdc4806d5ba2180456faba08ba`.
