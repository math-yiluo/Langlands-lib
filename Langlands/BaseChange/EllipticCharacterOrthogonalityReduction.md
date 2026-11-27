# Elliptic character orthogonality from three analytic statements

Lean module: `Langlands.BaseChange.EllipticCharacterOrthogonalityReduction`.

## Contents

- `isRegularElliptic_mul_conj_inv_iff`: `a b a⁻¹` is regular elliptic exactly when `b` is, because
  conjugate matrices have the same characteristic polynomial (`Matrix.charpoly_units_conj`).
- `EllipticCharacterOrthogonalityReductionStatement.{u, uV}`: the implication

  `EllipticOrbitalCoefficientStatement.{u, uV} → EllipticWeylIntegrationStatement.{u} →
   EllipticCoefficientTraceStatement.{u, uV} → EllipticCharacterOrthogonalityStatement.{u, uV}`.

- `ellipticCharacterOrthogonalityReduction`: its proof, with no further hypothesis.

The three premises are the elliptic orbital integral formula for square-integrable coefficients
(Clozel 1991, Proposition 5 (ii)), the Weyl integration formula on the regular elliptic set
modulo the center, and the elliptic part of the trace of a square-integrable coefficient
(Clozel 1991, (3.1) with Proposition 5 (i)). The conclusion is Clozel's Theorem 3 for `GL_n` in
the common-measure form of `EllipticCharacterOrthogonalityStatement`. This is the order of
Clozel's own proof of Theorem 3 (printed pp. 110–111, PDF pp. 121–122): the trace of a
coefficient is computed by Schur orthogonality and by the character formula, and the latter is
rewritten with the Weyl integration formula and Proposition 5.

## The proof

Fix `F`, `0 < n`, `G = GL_n(F)`, `Z` its center and `E ⊆ G ⧸ Z` the image of the regular
elliptic set. The measure of the conclusion is the measure `ν` of
`EllipticWeylIntegrationStatement`; it is chosen before the representations. Let `ρ`, `π`,
`cρ`, `cπ`, `Θρ`, `Θπ` be as in the conclusion.

1. **Data.** Let `μ` be the Haar measure `Measure.haar` on `G ⧸ Z` and `d` the formal degree of
   `π` for `μ` (`exists_isCentralFormalDegree`). Since `π` is irreducible its space is
   nontrivial; take `v ≠ 0` and a smooth functional `ℓ` with `ℓ(v) = 1`
   (`HarishChandraSchwartz.exists_smoothDual_eq_one` with `LevelZero.compactOpen_cofinal`).
   `EllipticCoefficientTraceStatement` gives `Φ` on `G ⧸ Z` with
   `Φ(gZ) = Θρ(g) conj ℓ(π(g) v)` on regular elliptic `g`, `0` elsewhere, `μ`-integrable, with
   `∫ Φ dμ = d⁻¹` if `ρ ≅ π` and `0` otherwise.
2. **The product.** The function `p = ellipticCharacterProduct cρ cπ hc Θρ Θπ hΘρ hΘπ` (module
   `Langlands.BaseChange.EllipticCharacterCentralProduct`) is the zero-extended product
   `Θρ conj Θπ` on `G ⧸ Z`, and it is Borel (`measurable_ellipticCharacterProduct`).
3. **Orbits of `Φ`.** For regular elliptic `b`, `EllipticOrbitalCoefficientStatement` applied
   to `π`, `γ = b` and `c = Θπ(b)` gives an integrable `o` with `o(gZ) = ℓ(π(g b g⁻¹) v)` and
   `∫ o dμ = d⁻¹ Θπ(b)`. Conjugation invariance of character values
   (`HasCharacterValue.conjugate` and uniqueness of local values) and of regular ellipticity
   give `Φ(g · bZ · g⁻¹) = Θρ(b) conj o(g)` for all `g`.
4. **Pointwise identity.** For every `x ∈ G ⧸ Z`,
   `p(x) = d ∫ Φ(g x g⁻¹) dμ(g)`. At `x = bZ` with `b` regular elliptic this is step 3 and
   `∫ conj o = conj ∫ o` (`integral_conj`); otherwise both sides vanish, since then every
   `g b g⁻¹` is not regular elliptic.
5. **Integrability.** `EllipticWeylIntegrationStatement` applied to `Ψ = ‖Φ‖` (integrable on
   `E`) shows that `B(x) = ∫ ‖Φ(g x g⁻¹)‖ dμ(g)` is `ν`-integrable. By step 3,
   `B(bZ) = ‖Θρ(b)‖ ∫ ‖o‖` and `‖p(bZ)‖ = ‖Θρ(b)‖ ‖d ∫ o‖ ≤ d B(bZ)`; off the elliptic set
   `p = 0`. Since `p` is measurable, it is `ν`-integrable (`Integrable.mono'`).
6. **Value.** `Φ` vanishes off `E`, so `∫_E Φ dμ = ∫ Φ dμ`. By step 4 and
   `EllipticWeylIntegrationStatement` for `Φ`,
   `∫ p dν = d ∫ (∫ Φ(g x g⁻¹) dμ(g)) dν(x) = d ∫_E Φ dμ = d ∫ Φ dμ`, which is `d · d⁻¹ = 1` if
   `ρ ≅ π` and `0` otherwise.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Source

Laurent Clozel, *Invariant harmonic analysis on the Schwartz space of a reductive p-adic
group*, in Barker and Sally (eds.), *Harmonic Analysis on Reductive Groups*, Progr. Math. 101,
Birkhäuser (1991), §3, Proposition 5 (printed p. 108, PDF p. 119) and Theorem 3 with its proof
(printed pp. 110–111, PDF pp. 121–122). Literature ID
`provided-698170812a35ff43dbc4156af9f67a8384f95d97d5836529575e646643af617b`, SHA-256
`c5cb36139e9cf3ed29fe1338a45488236cc69abdc4806d5ba2180456faba08ba`.
