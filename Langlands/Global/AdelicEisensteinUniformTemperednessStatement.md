# Uniform temperedness of Eisenstein series

Module `Langlands.Global.AdelicEisensteinUniformTemperednessStatement`, namespace
`Langlands.Global`. It states one proposition, `EisensteinUniformTemperednessStatement`, and
proves nothing.

## Source

P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered as
`delorme-2023-spectral-theorem-langlands` (published PDF numbering).

- §4.2, p.17: the space `ℱ_{Λ, μ, n}` of (4.5) and Proposition 4.1. Let `Λ` be a compact subset of
  `i𝔞_P^*`, `μ ∈ 𝔞_0^{G,+}` and `n ∈ ℕ`. `ℱ_{Λ, μ, n}` is the space of functions `F` on
  `G(𝔸) × Λ` such that, for every compact `Ω ⊆ G(𝔸)` and every `u ∈ U(𝔤_∞)`,
  `|R_u F(exp X ω, λ)| ≪ (1 + ‖X‖)^n e^{μ(X)}` for `X ∈ 𝔞_0^+`, `ω ∈ Ω`, `λ ∈ Λ`, and
  `F(exp X g, λ) = e^{λ(X)} F(g, λ)` for `X ∈ 𝔞_G`. Proposition 4.1: for `φ ∈ A^2_P` there is
  `n` with `(g, λ) ↦ E_P(g, φ, λ)` in `ℱ_{Λ, ρ, n}`.
- §2, p.7: Siegel domains (2.3) and their inclusion (2.4) in `Ω_{N_P} exp(𝔞_0^{+,P}) Ω`; p.8:
  `σ(g) = 1 + log ‖g‖` and (2.8), `σ ∼ 1 + ‖H_0‖` on Siegel domains.

Here `𝔞_0^+` is the closed positive chamber of `𝔞_0`. It contains `𝔞_G`, and `ρ` vanishes on
`𝔞_G`.

## The statement

The data are those of the Library's `EisensteinImaginaryAxisHolomorphyStatement`
(`Langlands/Global/AdelicEisensteinImaginaryHolomorphyStatement.lean`):

- a number field `F : Type` and a connected reductive `G`;
- a parabolic `p : P → G` with presentation `r : ParabolicRootPresentation p l a` and geometric
  unipotent radical `iU`;
- a maximal compact subgroup `K` with `hK : IsIwasawaCompact p K`;
- a closed matrix embedding `rho`, and `hsmooth`, `hcalc`;
- `φ ∈ A^2_P` (`IsSquareIntegrableInducedForm`).

Let `E : X^*(P) ⊗ ℂ → G(𝔸) → ℂ` and `D` satisfy three conditions:

- `D` contains the imaginary parameters;
- every `λ ↦ E λ g` is meromorphic in linear coordinates with domain of holomorphy `D`;
- `E λ = hK.eisensteinSeries φ λ` for `Re λ` sufficiently regular.

Let `e : ℝⁿ ≃ X^*(P) ⊗ ℝ` be real linear coordinates and `C ⊆ ℝⁿ` compact.

Conclusion: there is `m : ℕ` such that for every algebraic Siegel setup `(T, i, ν, T₀, j)`
(`IsSiegelAlgebraicSetup`), every threshold `t : ℝ≥0ˣ` and every compact `Ω ⊆ G(𝔸)` there is
`B : ℝ` with

`‖E(i e(x))(z · b · ω)‖ ≤ B · siegelModulus(b)^{1/2} · adelicLogHeight(z · b · ω)^m`

for every `x ∈ C`, every `z ∈ A_G` (`RestrictionSplitCentre.canonicalSubgroup F G`), every `b`
in the weak simple-root chamber `PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t`
(mapped to `G(𝔸)` by `positiveMap`) and every `ω ∈ Ω`.

`siegelModulus` and `adelicLogHeight` are those of
`Langlands/Global/AdelicWavePacketRapidDecaySiegelReduction.lean`.

## Correspondence with the source

- `λ ∈ Λ` is `i e(x)` with `x ∈ C`. Every compact subset of `i𝔞_P^*` has this form.
- The values `E(i e(x))` are those of the continued Eisenstein series `E_P(·, φ, λ)`. The
  continuation `(E, D)` is universal, and any two continuations agree on the intersection of
  their domains, by uniqueness of meromorphic continuation from the nonempty open regular
  region (`ParabolicRootPresentation.eqOn_of_regularParameter`). The imaginary parameters lie in
  `D`.
- `exp X` with `X ∈ 𝔞_0^+` is `z · b` with `z = exp X_G ∈ A_G` and `b` the torus coordinate. As
  explained in `AdelicWavePacketRapidDecaySiegelReduction.md`, `siegelModulus(b)^{1/2} =
  e^{ρ(X)}`. A threshold `t ≠ 1` changes the chamber by a compact box, which commutes with `b`
  and is absorbed into `Ω`, and changes `siegelModulus` by a bounded factor.
- The comparison of heights is made in two steps, separate from the threshold shift above.
  First, Delorme's norm and the raw norm `max(1, ‖·‖_ρ)` of the closed embedding `rho` are
  equivalent up to powers (`‖g‖₁^{1/c} ≪ ‖g‖₂ ≪ ‖g‖₁^c`; Delorme §2 with Beuzart-Plessis,
  Appendix A.1), not up to bounded factors: for `G = G_m` over `ℚ` and the embeddings
  `t ↦ t` and `t ↦ diag(t, t²)` the two norms at the point with real coordinate `r ≥ 1` and
  trivial finite coordinates are `r` and `r²`. Taking `1 + log` turns the power equivalence
  into a comparison by constants, `adelicLogHeight ∼ σ`. At the standard chamber
  representatives `z · b` (points of an enlarged covering Siegel domain), (2.8) then gives
  `adelicLogHeight(z b) ∼ 1 + ‖X‖`. Second, right translation by
  `ω ∈ Ω` changes the raw norm by at most bounded factors in both directions, by
  submultiplicativity of the height (`RepresentationGrowth.adelicHeight_mul_le`) and
  compactness of `Ω` and `Ω⁻¹`. Hence `adelicLogHeight(z b ω) ∼ 1 + ‖X‖` on these points. So
  Delorme's bound `(1 + ‖X‖)^n e^{ρ(X)}` implies the bound above with `m = n`, and conversely the
  bound above gives Delorme's bound for `u = 1`.
- The `𝔞_G`-equivariance of `ℱ_{Λ, ρ, n}` is not part of the statement. Its consequence
  `|E(z g)| = |E(g)|` for `z ∈ A_G` and imaginary `λ` is why `z` occurs in the bound only through
  `adelicLogHeight`.
- Only `u = 1` is stated. The derivatives `R_u E` are not.
- `m` is uniform in the setup, the threshold and `Ω`. Delorme's `n` does not depend on `Ω`. The
  estimate involves a setup `(T, i, ν, T₀, j)` only through the minimal parabolic and the
  maximal split torus `T` it contains, the positive and simple roots selected by `ν`, the
  derived torus `T₀` and the weight multiplicities. Cocharacters `ν` in the same chamber select
  the same roots, hence the same chamber and the same modulus; for example `ν` and `2ν` give the
  same estimate, although no conjugation carries one to the other. The pairs (minimal parabolic,
  maximal split torus contained in it) are conjugate under `G(F)`. Such a conjugation transports
  the chamber, the derived torus, the root multiplicities and the compact right factor. The left
  `G(F)`-invariance of the continued series moves the conjugating element into the compact right
  factor, and `adelicLogHeight` changes by at most a bounded factor under translation by a
  compact set. So the exponent is unchanged.
- Delorme works with standard parabolics containing a fixed minimal parabolic and a compact
  subgroup in good position. The statement quantifies over every presented parabolic with
  `P(𝔸)K = G(𝔸)` and every maximal compact `K` with that property. The transfers by rational
  conjugation of `P` and by comparison of compact subgroups (described in
  `AdelicWavePacketCompletenessReduction.md`, "Non-standard parabolics", and in
  `AdelicEisensteinConvergenceStatement.md`) are part of the proof obligation.

Delorme's proof of Proposition 4.1 is short. It applies Mœglin–Waldspurger, Lemma I.4.1,
uniformly to a bounded family of automorphic forms. The inputs are the uniform moderate growth
of the continued series on bounded parameter sets (Bernstein–Lapid, J. Amer. Math. Soc. 37
(2024), the Corollary at the end of §8.6, p.226, which Delorme cites as Corollary 8.6), its
holomorphy on `i𝔞_P^*`, and the formulas (4.1)–(4.2) for its constant terms, whose exponents
are subunitary for unitary `λ` (Lapid 2011, Lemma 6).

## Scope

The statement does not assert holomorphy, the constant term formula, temperedness of
derivatives or the weak constant term. Nothing is proved here.
