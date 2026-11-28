# The elliptic part of the trace of a square-integrable coefficient from two analytic statements

Lean module: `Langlands.BaseChange.EllipticCoefficientTraceReduction`.

## Contents

- `isRegularSemisimple_inv_mul_mul_iff`: `a⁻¹ g a` is regular semisimple exactly when `g` is,
  because conjugate matrices have the same characteristic polynomial
  (`Matrix.charpoly_units_conj'`).
- `EllipticCoefficientTraceReductionStatement.{u, uV}`: the implication

  `SquareIntegrableCoefficientCharacterFormulaStatement.{u, uV} →
   SquareIntegrableCoefficientNonellipticVanishingStatement.{u, uV} →
   EllipticCoefficientTraceStatement.{u, uV}`.

- `ellipticCoefficientTraceReduction`: its proof, with no further hypothesis.

The first premise is Clozel's character formula (3.1) for the conjugate of a `K`-finite
coefficient of a square-integrable representation, with the trace written through the trace
coefficient `ψ^ρ_H` (Clozel 1991, §3, Corollary 4 and the proof of Theorem 3). The second is the
vanishing of the non-elliptic part of the integral of a class function times such a
coefficient (Weyl integration formula and Clozel's Proposition 5 (i)). The third ingredient is
proved in the Library: the Schur orthogonality computation of the same trace,
`exists_integral_traceCoefficient_mul_star_coefficient` (module
`Langlands.BaseChange.CoefficientTraceSchur`). This is the order of Clozel's argument in the
proof of Theorem 3: the trace of the coefficient is computed twice, by Schur orthogonality and
by the character formula, and only the elliptic part of the latter survives.

## The proof

Fix `F`, `0 < n`, `G = GL_n(F)`, `Z` its center, and `μ`, `ρ`, `π`, `cρ`, `cπ`, `d`, `Θρ`, `v`,
`ℓ` as in `EllipticCoefficientTraceStatement`.

1. **A compact open subgroup fixing `v`.** Since `π` is smooth, some compact open subgroup `H`
   of `G` fixes `v` (`exists_compactOpen_fixing_finite`, applied to the single vector `v`).
2. **Schur orthogonality.** `exists_integral_traceCoefficient_mul_star_coefficient` gives an
   integrable `T` on `G ⧸ Z` with `T(gZ) = ψ^ρ_H(g) conj ℓ(π(g) v)` and
   `∫ T dμ = d⁻¹ conj ℓ(v)` if `ρ ≅ π`, `0` otherwise.
3. **Character formula.** `SquareIntegrableCoefficientCharacterFormulaStatement` applied to `ρ`
   gives `Θ : G → ℂ` with `HasCharacterValue ρ _ g (Θ g)` at every regular semisimple `g`, and
   then, for `μ`, `π`, `cρ`, `cπ`, `v`, `ℓ`, an integrable `Ψ` on `G ⧸ Z` with
   `Ψ(gZ) = Θ(g) conj ℓ(π(g) v)` and `∫ Ψ dμ = ∫ T dμ` (for the `H` and `T` of steps 1–2).
4. **`Θ` is a class function on the regular semisimple set.** For regular semisimple `g` and
   any `a`, `a⁻¹ g a` is regular semisimple (`isRegularSemisimple_inv_mul_mul_iff`), and the
   character value of `ρ` at `a⁻¹ g a` is the one at `g` (`HasCharacterValue.conjugate`); by
   uniqueness of character values (`HasCharacterValue.unique`), `Θ(a⁻¹ g a) = Θ(g)`.
5. **Non-elliptic part.** `SquareIntegrableCoefficientNonellipticVanishingStatement` applied to
   `μ`, `π`, `Θ`, `v`, `ℓ` and `Ψ` gives an integrable `Φ'` on `G ⧸ Z`, equal to `0` at
   regular elliptic `gZ` and to `Ψ(gZ)` elsewhere, with `∫ Φ' dμ = 0`.
6. **Conclusion.** Put `Φ = Ψ − Φ'`. At a regular elliptic `g`, `Φ(gZ) = Θ(g) conj ℓ(π(g) v)`
   and `Θ(g) = Θρ(g)`, both being character values of `ρ` at `g` (`HasCharacterValue.unique`,
   since regular elliptic elements are regular semisimple); elsewhere `Φ(gZ) = 0`. So `Φ` has
   the required values, it is integrable, and
   `∫ Φ dμ = ∫ Ψ dμ − ∫ Φ' dμ = ∫ T dμ`, which is the value from step 2.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Source

Laurent Clozel, *Invariant harmonic analysis on the Schwartz space of a reductive p-adic
group*, in Barker and Sally (eds.), *Harmonic Analysis on Reductive Groups*, Progr. Math. 101,
Birkhäuser (1991), §3, Corollary 4 and Proposition 5 (printed p. 108, PDF p. 119) and the proof
of Theorem 3 with formula (3.1) (printed pp. 110–111, PDF pp. 121–122). Literature ID
`provided-698170812a35ff43dbc4156af9f67a8384f95d97d5836529575e646643af617b`, SHA-256
`c5cb36139e9cf3ed29fe1338a45488236cc69abdc4806d5ba2180456faba08ba`.
