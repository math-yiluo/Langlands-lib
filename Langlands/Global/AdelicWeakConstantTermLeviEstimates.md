# Weighted Levi estimates for the pairing with the weak constant term

This module splits the absolute convergence of Delorme's pairing (3.7) with a weak constant term,
`WeakConstantTermPairingIntegrableStatement` of
`Langlands.Global.AdelicWeakConstantTermComponentExtraction`, into two weighted `L²` estimates on
`K × M(F) \ M(𝔸)^1`. One is a Schwartz estimate for the square-integrable inducing forms. The
other is a temperedness estimate for the weak constant term. The integration step is the
Cauchy–Schwarz inequality and is proved here. The module contains:

- the proposition `SquareIntegrableInducedFormLeviSchwartzStatement`;
- the proposition `WeakConstantTermLeviTemperedStatement`;
- `weakConstantTermPairingIntegrable_of_leviEstimates`: the two propositions imply
  `WeakConstantTermPairingIntegrableStatement`;
- `weakConstantTermComponentPairingIntegrable_of_leviEstimates`: the two propositions imply
  `WeakConstantTermComponentPairingIntegrableStatement` of
  `Langlands.Global.AdelicWeakConstantTermPairingPolynomials`.

The two propositions are stated and not proved in this module. Both theorems use only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Source

P. Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023), 109107,
registered as `delorme-2023-spectral-theorem-langlands` (published PDF, SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`):

- §2, p. 8: the quotient functions `f_{[G]_P}(g) = inf_{γ ∈ M_P(F) N_P(𝔸)} f(γ g)` (2.6),
  the height `σ(g) = 1 + log ‖g‖` with (2.7)–(2.8), the function `Ξ^{[G]}`, Lemma 2.1 and
  (2.10), `∫_{[G]} (1 + σ_{[G]}(x))^{-d_G} Ξ^{[G]}(x)^2 dx < ∞`;
- Definition 3.3 and Proposition 3.5, pp. 11–12: tempered automorphic forms, characterized by
  bounds `≪ Ξ σ^d` and equivalently by weighted `L²` conditions on derivatives;
- Lemma 3.8 (ii), p. 14: `φ_P^w ∈ A_P^{temp}(G)` for tempered `φ`;
- §3.4, p. 15: `A^2(G) ⊂ C(G)` by Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein
  Series* (1995), Lemmas I.4.1 and I.4.11, and the absolute convergence of (3.7) for
  `φ ∈ A^2_P(G)` and `ψ ∈ A_P^{temp}(G)`, deduced from this inclusion, (2.10) and
  Proposition 3.5.

## The weight

For a standard index `J` with Levi subgroup `M = M_J`, the weight at a point `z = (k, M(F) m)`
of `K × M(F) \ M(𝔸)^1` is

`σ_{[M]}(m) = rationalLogHeight F M (rho.restrict (𝓕.l J ≫ 𝓕.p J)) (normOneQuotientInclusion F M (M(F) m))`,

Delorme's logarithmic height `1 + log max(1, inf_{γ ∈ M(F)} ‖γ m‖)` on `M(F) \ M(𝔸)` for the
norm of the matrix embedding `rho` of `G` restricted to `M` along `M → P → G`
(`MatrixRepresentation.restrict`). It does not depend on `k` or on the representative `m`, and
it is at least `1` (`one_le_rationalLogHeight`). The Levi subgroup is a closed subgroup of `G`,
so the restriction of the norm of a closed embedding of `G` is a norm of `M` in the sense of
Mœglin–Waldspurger I.2.2, and different choices change `σ_{[M]}` only up to positive constant
factors. The exponents in the two propositions absorb such factors.

## `SquareIntegrableInducedFormLeviSchwartzStatement`

Hypotheses: those of `WeakConstantTermComponentPairingIntegrableStatement` on `F`, `G`, `K`,
`rho`, `hsmooth`, `hcalc` and the family `𝓕` with `hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K`, a
standard index `J`, and `φ` with
`IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc (𝓕.p J) (𝓕.iU J) (𝓕.l J) φ`.
Conclusion: for every `n : ℕ`, the function

`z ↦ φ(m_z k_z) σ_{[M]}(m_z)^n`, with `m_z = Quotient.out z.2` and `k_z = z.1`,

is in `L²` (`MemLp … 2`) for `𝓕.squareIntegrablePairingMeasure K hK.isCompact J`, the Haar
probability of `K` times the quotient Haar measure of `M(F) \ M(𝔸)^1`.

Correspondence. For `m ∈ M(𝔸)^1` the factor `δ_P(m)` is `1`, and `m ↦ φ(m k)` is a
square-integrable automorphic form of the Levi subgroup. Mœglin–Waldspurger I.4.1 and I.4.11
give `|φ(m k)| ≪_n Ξ^{[M]}(m) σ_{[M]}(m)^{-n}` for every `n`, uniformly in `k` by
`K`-finiteness (Delorme's `A^2 ⊂ C`). With (2.10) for `M`,
`∫_{[M]^1} Ξ^{[M]}(m)^2 σ_{[M]}(m)^{-d_M} dm < ∞`, this gives the weighted `L²` bound for every
`n`. The proposition is a consequence of the Schwartz estimate and is weaker than it. As in the
target, `K` is any maximal compact subgroup with `P_∅(𝔸) K = G(𝔸)`, with the space `A^2_P` and
the measure of this `K`; Delorme assumes `K` in good position.

## `WeakConstantTermLeviTemperedStatement`

Hypotheses: those of `WeakConstantTermPairingIntegrableStatement`, through
`IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ`, a standard index `J` and `ψ`
with `𝓕.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J Φ ψ`.
Conclusion: for every `x ∈ 𝓕.positiveSplitComponent J` there is `n : ℕ` such that

`z ↦ ψ(x m_z k_z) / σ_{[M]}(m_z)^n`

is in `L²` for the same measure. The point `x m_z k_z` is written exactly as in
`squareIntegrablePairingIntegrand`.

Correspondence. By Proposition 3.5, `Φ` is tempered, and by Lemma 3.8 (ii) `ψ = Φ_P^w` is in
`A_P^{temp}(G)`: on Siegel domains of `[G]_P`, `|ψ(g)| ≪ e^{ρ(H_0(g))} (1 + ‖H_0(g)‖)^d`.
At `g = x m k` with `x` fixed in `𝔄_P` and `m ∈ M(𝔸)^1` this is
`|ψ(x m k)| ≪_x Ξ^{[M]}(m) σ_{[M]}(m)^d` ((2.8) and Lemma 2.1 of Delorme, for `M`). With (2.10)
for `M`, `ψ(x · ) σ_{[M]}^{-n}` is in `L²` once `2n - 2d ≥ d_M`. The exponent may depend on
`x`. The compact-subgroup scope is that of the target.

## Proof of `weakConstantTermPairingIntegrable_of_leviEstimates`

Take the data of `WeakConstantTermPairingIntegrableStatement`, a weak constant term `ψ`, an
inducing form `φ` and `x ∈ 𝔄_P`. `WeakConstantTermLeviTemperedStatement` gives `n` with
`g(z) = ψ(x m_z k_z) / σ_{[M]}(m_z)^n` in `L²`, and
`SquareIntegrableInducedFormLeviSchwartzStatement` with this `n` gives
`f(z) = φ(m_z k_z) σ_{[M]}(m_z)^n` in `L²`. Hölder's inequality for the conjugate exponents
`2, 2` (`MemLp.integrable_mul`, with `MemLp.star` for the conjugate of `g`) gives integrability
of `f · conj g`, hence of `δ_P(x)^{1/2} f · conj g`. This function is the pairing integrand:

- `φ(x m k) = δ_P(x)^{1/2} φ(m k)` by `splitComponentEquivariant_apply`, since `φ` is
  split-component equivariant (second conjunct of `IsSquareIntegrableInducedForm`);
- `σ_{[M]}(m)^n` is real and nonzero, so `σ^n · conj(ψ(x m k) / σ^n) = conj ψ(x m k)`
  (`star_div₀`, `Complex.conj_ofReal`, `field_simp`).

`weakConstantTermComponentPairingIntegrable_of_leviEstimates` composes this theorem with
`weakConstantTermComponentPairingIntegrable_of_weakConstantTerm`.
