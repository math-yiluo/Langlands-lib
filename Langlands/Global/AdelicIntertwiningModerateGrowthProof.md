# Moderate growth of regular adelic intertwining integrals: proof

Module `Langlands.Global.AdelicIntertwiningModerateGrowthProof` proves the published proposition
`Langlands.Global.IntertwiningModerateGrowthStatement.{u}` (module
`Langlands.Global.AdelicIntertwiningAutomorphyStatement`) as the theorem
`Langlands.Global.intertwiningModerateGrowth`. It also proves one auxiliary lemma. Lean reports
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Auxiliary lemma

`subsingleton_adelicGroupPoints_of_closed_zeroMatrix`: if `rho : MatrixRepresentation G (Fin 0)`
is a closed immersion, the adelic points of `G` form a subsingleton. The matrix map on points is
injective (`MatrixRepresentation.pointMatrix_injective`) and its target, the `0 × 0` matrices,
has one element.

## The proof

Fix the data of the statement and write `T λ` for
`hK.intertwiningOperator hK' iU l iV c π' w φ λ`, `I λ` for the intertwining integral
`hK.intertwiningIntegral iU (iV ≫ q) w φ λ`, so that
`T λ g = hK'.heightPower (-weylParameter l c π' λ) g * I λ g`, and `H` for the adelic height
`adelicHeight F G rho`.

**Size zero.** If `N = 0`, the adelic points form a subsingleton, so every function on them is
constant. The threshold `0` and the bound `‖T λ g‖ ≤ (‖T λ 1‖ + 1) * norm(g)^0` work.

**Positive size.** Let `N > 0`.

1. `eisensteinGlobalMajorant` (module `AdelicEisensteinGlobalMajorant`), applied to `φ`, which is
   left invariant under `U(𝔸)M(F)` and of moderate growth, gives a threshold `R`. This is the
   threshold of the theorem. For an `R`-regular `λ` it gives a summable nonnegative `b` on
   `P(F) \ G(F)` and `e ≥ 0` with `‖φ_λ(γ g)‖ ≤ b(γ) H(g)^e` for every Eisenstein term.
2. `exists_integrable_unfolding_majorant` (module `AdelicEisensteinUnfoldingGlobalMajorant`), with
   `Λ` the rational stabilizer `intertwiningRationalSubgroup F p iU (iV ≫ q) w` of the
   intertwining integral, turns `b` into a nonnegative function `B` on the quotient
   `(V(F) ∩ wU(𝔸)w⁻¹) \ V(𝔸)`, integrable for `intertwiningMeasure`, with
   `‖φ_λ(w⁻¹ x g)‖ ≤ B(x) H(g)^e` for every class `x` (at its chosen representative) and every
   `g`. Its fibre hypothesis (two rational points of `V` with the same coset `P(F) w⁻¹ δ` differ
   by an element of `Λ`) is `mul_inv_mem_intertwiningRationalSubgroup` (module
   `AdelicIntertwiningConvergenceReduction`), applied as in the proof of
   `intertwiningAbsoluteConvergence_of_eisenstein`.
3. Hence `‖I λ g‖ ≤ ∫ B(x) H(g)^e dx = (∫ B) H(g)^e` (`norm_integral_le_of_norm_le`,
   `integral_mul_const`).
4. `IsIwasawaCompact.exists_norm_heightPower_le_adelicHeight` (module
   `AdelicHeightPowerPolynomialBound`) for `q`, `K` and the parameter `-weylParameter l c π' λ`
   gives `C > 0` and `e' ≥ 0` with `‖m_Q(g)^{-wλ}‖ ≤ C H(g)^{e'}`.
5. Multiplying, `‖T λ g‖ ≤ C (∫ B) H(g)^{e' + e}` (`Real.rpow_add`, since `H ≥ 1`).
   `adelicHeight_eq_scalar_mul_sourceNorm` writes `H = s · adelicSourceNorm` with
   `s = N^{Σ_v mult(v)} > 0`, so
   `‖T λ g‖ ≤ (C (∫ B) s^{e'+e} + 1) · adelicSourceNorm(g)^{e'+e}`, which is
   `HasModerateGrowthFunction F G rho (T λ)`.

The constant and exponent depend on `λ`; the threshold does not.

## Provenance

This is the moderate-growth part of Mœglin–Waldspurger, *Spectral decomposition and Eisenstein
series* (1995), II.1.6, Proposition (i), printed pp. 87–88, registered as
`moeglin-waldspurger-1995-spectral-decomposition` (chapter file `06.1_pp_78_100_Definitions.pdf`,
SHA-256 `948dbfd356c2f068c1dc793a52e4c700334eb5236b740f1c775da535b747111c`, PDF pp. 10–11). The
source bounds the integral by an integral over the compact quotient `U'(k) \ U'(𝔸)` of the
Eisenstein series of absolute values and uses II.1.5. The Lean proof uses the pointwise form of
that unfolding provided by the two Library theorems above, with a global polynomial weight in the
external argument instead of uniformity on compact sets.
