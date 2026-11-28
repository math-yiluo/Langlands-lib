# Elliptic matching of supercuspidal coefficients from three analytic statements

The module `Langlands.BaseChange.SupercuspidalCoefficientEllipticMatchingReductionStatement`
states, as the proposition
`SupercuspidalCoefficientEllipticMatchingReductionStatement.{u, v, uV, uW}`, the implication

`SupercuspidalWindowCoefficientCuspFormStatement.{u, v, uW} →`
`SupercuspidalWindowCoefficientCuspFormStatement.{u, u, uV} →`
`SupercuspidalWindowSchurOrthogonalityStatement.{u, v, uW} →`
`SupercuspidalWindowSchurOrthogonalityStatement.{u, u, uV} →`
`SupercuspidalCoefficientEllipticOrbitalStatement.{u, v, uW} →`
`SupercuspidalCoefficientEllipticOrbitalStatement.{u, u, uV} →`
`SupercuspidalCoefficientEllipticMatchingStatement.{u, v, uV, uW}`.

Each premise is used twice: at `{u, v, uW}` for the extension `E : Type v` and the
representation `τ` on `W : Type uW`, and at `{u, u, uV}` for the base field `F : Type u`
regarded as an extension of itself (`σ = 1`, `l = 1`) and the representation `π` on
`V : Type uV`. The module states the implication and does not prove it.

## The premises

- `SupercuspidalWindowCoefficientCuspFormStatement` (module of the same name): a coefficient
  `x ↦ λ(τ(x)⁻¹ v)` of the contragredient of a supercuspidal `τ`, multiplied by the determinant
  window `determinantWindow F m` and by `ψ(det x)` for a locally constant `ψ`, is a
  Schwartz–Bruhat function with vanishing constant terms.
- `SupercuspidalWindowSchurOrthogonalityStatement`: for an irreducible supercuspidal `τ` and a
  Haar measure, there is `d ≠ 0` such that the coefficient cut off by
  `determinantWindow F (n [E : F])` acts as `u ↦ d λ(u) v`.
- `SupercuspidalCoefficientEllipticOrbitalStatement`: at `δ` associated with a regular elliptic
  `γ`, `x ↦ b(x) λ(τ(x⁻¹ δ x^σ)⁻¹ v)` has compact support and integral
  `Θ · tr(τ(φ) ∘ A)`, where `Θ` is the value at `δ⁻¹` of the twisted character of `A⁻¹` and
  `φ = b · λ(τ(·)⁻¹ v)`.

## How the conclusion follows

Fix `λ(A v) ≠ 0` and `λ'(w) ≠ 0`, let `φ` be the cut-off coefficient of `τ` with the window
`b_E = determinantWindow F (n l)` and `f₁` that of `π` with `b_F = determinantWindow F n`, and
put `T_E = tr(τ(φ) ∘ A) = d_E λ(A v) ≠ 0` and `T_F = tr π(f₁) = d_F λ'(w) ≠ 0` (Schur
orthogonality). Let `f` be the coefficient of `π` cut off by `determinantWindow F (n l)` and
multiplied by `κ · 1_{N_{E/F}(E^×)}(det x)`, `κ = c T_E / T_F`; the norm subgroup is open
(`IsCyclicAlgebra.normRange_isOpen_finiteIndex`), so the cusp-form statement applies to `φ`
and `f`. At a regular elliptic non-norm `γ`, `det γ ∉ N_{E/F}(E^×)`
(`EllipticNormCriterionStatement`), so `f(γ) = 0`.

For associated `(δ, γ)` with `γ` regular elliptic, let `μδ`, `μγ` be associated right Haar
measures on the σ-centralizer `T_δ` and the centralizer `G_γ`, and `νδ`, `νγ` compatible
quotient measures. The Weil formula in `QuotientIntegration.IsCompatible`, applied to the
continuous compactly supported function `x ↦ b_E(x) c(x⁻¹ δ x^σ)`, gives
`C_δ · Λ_σ(φ, δ) = b_E(δ) · Θ' · T_E`, where `C_δ = ∫_{T_δ} b_E dμδ` (the inner integral
`∫_{T_δ} b_E(t x) dμδ(t)` does not depend on `x`, because the scalar uniformizer of `F` lies in
`T_δ` and shifts `ord_F N_{E/F} det` by `n l`), and `Θ' = c a` by hypothesis. In the same way
`C_γ · Λ(f, γ) = κ · b_E(δ) · a · T_F` with `C_γ = ∫_{G_γ} b_F dμγ`, using
`det γ = N_{E/F}(det δ)` (`IsNormAssociated.norm_determinant_eq`). Associated measures give
`C_δ = C_γ`, because `b_E(x⁻¹ t x) = b_E(t)` and `b_E` restricted to `GL_n(F)` is `b_F`
(`ord_F N_{E/F}(y) = l ord_F y` for `y ∈ F^×`). The constant is finite and positive: the
orbital statement applied to a second coefficient that does not vanish at `δ` shows that
`{t ∈ T_δ : b_E(t) ≠ 0}` is relatively compact, and it is a nonempty open subset of `T_δ`.
Hence `Λ_σ(φ, δ) = Λ(f, γ)`, and `tr(τ(φ) ∘ A) = T_E ≠ 0`.

## Sources and provenance

This is a derived reduction formulated for this Library: it carries out steps 1–5 of the
proof sketch in `Langlands/BaseChange/SupercuspidalCoefficientEllipticMatchingStatement.md`
(Henniart–Lemaire 2011, II.4.10 and II.6.3–II.6.4; Arthur–Clozel 1989, Chapter 1,
Lemma 1.4), with the three analytic inputs isolated as separate statements.
