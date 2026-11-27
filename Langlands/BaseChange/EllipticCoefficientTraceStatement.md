# The elliptic part of the trace of a square-integrable coefficient of GL_n

Lean module: `Langlands.BaseChange.EllipticCoefficientTraceStatement`. The file states the
proposition `EllipticCoefficientTraceStatement.{u, uV}` and does not prove it.

## The statement

Let `F : Type u` be a nonarchimedean local field of characteristic zero, `0 < n`,
`G = GL_n(F)`, `Z` its center and `G ⧸ Z` with its Borel σ-algebra. Take

- a Haar measure `μ` on `G ⧸ Z`;
- representations `ρ` on `V` and `π` on `W` (both `V W : Type uV`) of `G`, irreducible and
  square-integrable modulo the center (`IsSquareIntegrable`);
- unitary central characters `cρ`, `cπ` of `ρ` and `π` with the same underlying character;
- the formal degree `d` of `π` for `μ` (`IsCentralFormalDegree μ π d`);
- values `Θρ g` of the character of `ρ` at every regular elliptic `g`
  (`HasCharacterValue ρ _ g (Θρ g)`);
- a vector `v : W` and a smooth functional `ℓ` of `π`.

Then there is `Φ : G ⧸ Z → ℂ` with

`Φ(gZ) = Θρ(g) · conj ℓ(π(g) v)` if `g` is regular elliptic, `Φ(gZ) = 0` otherwise,

and `Φ` is `μ`-integrable with

`∫_{G/Z} Φ dμ = d⁻¹ conj ℓ(v)` if `ρ ≅ π`, and `0` otherwise.

Here `conj` is complex conjugation (`star`), and `ρ ≅ π` is `Nonempty (ρ.Equiv π)`. The
function descends to `G ⧸ Z` because `ρ` and `π` have the same unitary central character.

## Source and derivation

Laurent Clozel, *Invariant harmonic analysis on the Schwartz space of a reductive p-adic
group*, in Barker and Sally (eds.), *Harmonic Analysis on Reductive Groups*, Progr. Math. 101
(1991), §3:

- Corollary 4, printed p. 108 (PDF p. 119): for tempered `π` and `f` in the Schwartz space
  `C(G)`, `trace π(f) = ∫ Θ_π f`.
- Proof of Theorem 3, printed p. 110 (PDF p. 121), formula (3.1): for `f ∈ C(G/Z)`,
  `trace π₁(f) = ∫_{Z\G} Θ_{π₁}(x) f(x) dx`, the integral being absolutely convergent; for
  non-trivial central characters, `f ∈ C(G, ξ⁻¹)` (printed p. 111, PDF p. 122). It is applied
  to `f` the conjugate of a `K`-finite matrix coefficient of `π₂`, whose trace is given by the
  Schur orthogonality relations, and rewritten with the Weyl integration formula.
- Proposition 5 (i), printed p. 108 (PDF p. 119): the orbital integrals of a `K`-finite matrix
  coefficient of a square-integrable representation vanish at regular elements of non-elliptic
  Cartan subgroups.

The statement is the following consequence. Let `f(x) = conj ℓ(π(x) v)`, a `K`-finite
coefficient of the complex conjugate of `π`, which is square-integrable with central character
inverse to that of `ρ`. Choose an invariant inner product on `π` and write `ℓ = ⟨·, w⟩`. By the
Schur orthogonality relations, `ρ(f) = ∫_{G/Z} f(x) ρ(x) dx` is `0` if `ρ ≇ π`, and for `ρ = π`
it is the operator `u ↦ d⁻¹ ⟨u, v⟩ w`, of trace `d⁻¹ ⟨w, v⟩ = d⁻¹ conj ℓ(v)`. By (3.1) this
trace is the absolutely convergent integral `∫_{G/Z} Θ_ρ f`. Writing that integral with the
Weyl integration formula, the contribution of every non-elliptic Cartan subgroup vanishes by
Proposition 5 (i), and the non-regular elements form a null set. What remains is the integral
over the regular elliptic set, which is `∫ Φ dμ`; it is absolutely convergent because the
integral in (3.1) is.

The module `Langlands.BaseChange.EllipticCharacterOrthogonalityReduction` derives the elliptic
orthogonality relations of Clozel's Theorem 3 for `GL_n` from this statement, the elliptic
orbital integral formula `EllipticOrbitalCoefficientStatement` and the Weyl integration formula
`EllipticWeylIntegrationStatement`.

Literature ID `provided-698170812a35ff43dbc4156af9f67a8384f95d97d5836529575e646643af617b`,
SHA-256 `c5cb36139e9cf3ed29fe1338a45488236cc69abdc4806d5ba2180456faba08ba`.
