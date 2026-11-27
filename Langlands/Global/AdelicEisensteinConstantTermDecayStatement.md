# Decay of Eisenstein series minus their constant term along a standard parabolic

Module `Langlands.Global.AdelicEisensteinConstantTermDecayStatement`, namespace
`Langlands.Global`. It states one proposition, `EisensteinConstantTermDecayStatement`, and proves
nothing.

## Source

P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered as
`delorme-2023-spectral-theorem-langlands` (published PDF numbering).

- §3.1, pp.10–11: Lemma 3.1, a variant of Mœglin–Waldspurger, Lemma I.2.10, for a standard
  parabolic `P`. Fix a compact open `K'_f ⊆ G(𝔸_f)`, `u ∈ U(𝔤_∞)`, `c > 0`, a decay parameter
  `τ > 0` (written `t` in the source; here `t` is the chamber threshold) and `n`. Then there are
  finitely many `u_i ∈ U(𝔤_∞)` and `c_i > 0` with the following property. Let `φ` be a smooth
  function on `U_0(F) \ G(𝔸)`, right invariant by `K'_f`, and let `r > 0` and `λ ∈ 𝔞^*_{M_0}`.
  Suppose that
  `|R_{u_i} φ(a g)| ≤ c_i (1 + ‖H_G(a)‖)^r e^{λ(H_{P_0}(g))} (1 + ‖H_{P_0}(g)‖)^n` for
  `a ∈ A_G^∞` and `g ∈ G(𝔸)^1 ∩ 𝔰_G`. Then
  `|R_u(φ − φ_P)(a g)| ≤ c (1 + ‖H_G(a)‖)^r e^{(λ − τ β_P)(H_{P_0}(g))} (1 + ‖H_{P_0}(g)‖)^n`
  for the same `a` and `g`, where `β_P(X) = inf_{α ∈ Δ_0 \ Δ_0^P} α(X)`. This is the second
  statement of the lemma. The source writes `N` for both the number of the `u_i` and the
  exponent `n`. Both `r > 0` and `τ > 0` are hypotheses of the lemma.
- §4.2, p.17: the spaces `ℱ_{Λ, μ, n}` of (4.5) and Proposition 4.1: for `Λ ⊆ i𝔞_P^*` compact
  and `φ ∈ A^2_P` there is `n` with `E_P(·, φ, ·) ∈ ℱ_{Λ, ρ, n}`, that is
  `|R_u E_P(exp X ω, φ, λ)| ≪ (1 + ‖X‖)^n e^{ρ(X)}` for `X ∈ 𝔞_0^+`, `ω` in a compact set and
  `λ ∈ Λ`, for every `u ∈ U(𝔤_∞)`.
- §5.1, p.19, proof of Lemma 5.1: after the bound for `φ_Q − φ^w_Q`, "one uses Lemma 3.1 to have
  a similar bound for `|φ − φ_Q|`". Proof of Lemma 5.3, pp.19–20: Lemma 5.1 is carried over to
  Eisenstein series using Proposition 4.1, uniformly for `λ` in a bounded subset of `i𝔞_P^*`.

The original lemma is C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
series* (1995), registered as `moeglin-waldspurger-1995-spectral-decomposition`, Lemma I.2.10,
printed pp.30–34, for a maximal standard parabolic and its omitted simple root.

## The statement

The data are those of `EisensteinWeakConstantTermApproximationStatement`
(`Langlands/Global/AdelicEisensteinWeakConstantTermApproximationStatement.md`) up to the subset
`J`:

- a number field `F : Type` and a connected reductive `G` over `F`;
- a parabolic `p : P → G` with presentation `r : ParabolicRootPresentation p l a` and geometric
  unipotent radical `iU`;
- a maximal compact subgroup `K` of `G(𝔸)` with `hK : IsIwasawaCompact p K`;
- a closed matrix embedding `rho` of `G`, and `hsmooth`, `hcalc`;
- `φ ∈ A^2_P` (`IsSquareIntegrableInducedForm`);
- `E : X^*(P) ⊗ ℂ → G(𝔸) → ℂ` and `D` such that `D` contains the imaginary parameters, every
  `λ ↦ E λ g` is meromorphic in linear coordinates with domain of holomorphy `D`, and
  `E λ = hK.eisensteinSeries φ λ` for `Re λ` sufficiently regular;
- real linear coordinates `e : ℝⁿ ≃ X^*(P) ⊗ ℝ` and a compact `C ⊆ ℝⁿ`;
- an algebraic Siegel setup `(T, i, ν, T₀, j)` (`IsSiegelAlgebraicSetup`) such that `K` is an
  Iwasawa subgroup for its standard minimal parabolic `Standard.parabolicHom i ν ∅`;
- a subset `J` of the simple roots `Δ = simpleRelativeRoots i ν` with `J ≠ Δ`.

Let `N_Q → G` be `Standard.unipotentHom i ν J`, the unipotent radical of the standard parabolic
`Q = Q_J`, and for a function `f` on `G(𝔸)` let
`f_Q(g) = subgroupConstantTerm F (Standard.unipotentHom i ν J) f g`, the constant term
`∫_{N_Q(F) \ N_Q(𝔸)} f(u g) du` for the quotient Haar measure of total mass one
(`Langlands/Global/AdelicEisensteinConstantTermStatement.lean`). Write `|β(b)|` for the idele
norm of `β(b)` at a point `b` of the positive torus `A_{T₀}`, so that
`logNormHom F T₀ b (j ≫ β) = log |β(b)|`, and `δ(b) = siegelModulus(b)`.

Conclusion: there is `m : ℕ` such that for every threshold `t : ℝ≥0ˣ`, every compact
`Ω ⊆ G(𝔸)` and every `k : ℕ` there is `B` with

`‖E(i e(x))(z b ω) − E(i e(x))_Q(z b ω)‖ ≤ B · δ(b)^{1/2} · (1 + R)^m · e^{−k s}`

for `x ∈ C`, `z ∈ A_G` (`RestrictionSplitCentre.canonicalSubgroup F G`), `b` in the weak
simple-root chamber `|β(b)| ≥ t` (`PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t`,
mapped to `G(𝔸)` by `positiveMap`), `ω ∈ Ω`, and all real `R` and `s` with `|log |β(b)|| ≤ R`
for every `β ∈ Δ` and `s ≤ log |α(b)|` for every `α ∈ Δ \ J`. The exponent `m` is chosen before
`t`, `Ω` and `k`, and `B` after them.

## Correspondence with the source

Take first `P` standard and `K` in good position, as in Delorme.

- **The constant term.** `Standard.unipotentHom i ν J` is the composite of
  `Standard.unipotentToParabolic i ν J` and `Standard.parabolicHom i ν J`
  (`Standard.unipotentToParabolic_comp`); the first is the unipotent radical in the standard
  parabolic datum (`ParabolicDatum.standard`), and it is the radical `iU ⟨J, _⟩` of the family
  `StandardParabolicFamily.ofMaximalSplitTorus`. So `f_Q` is the constant term `φ_Q` of
  Delorme along `Q` (Mœglin–Waldspurger I.2.6, with `N_Q(F) \ N_Q(𝔸)` of volume one).
- **The bound.** With `X = H_0(b)`, `δ(b)^{1/2} = e^{ρ(X)}` (`siegelModulus` is
  `δ_{P_0}(b) = e^{2ρ_0(H_0(b))}`). Apply Lemma 3.1, second statement, with `P` replaced by
  `Q`, `u = 1`, `λ = ρ`, `r = 1`, the input exponent `n` of Proposition 4.1, and the decay
  parameter `τ = k d` if `k ≥ 1` and `τ = 1` if `k = 0`, where `d > 0` is the constant of the
  item on root coordinates. So `τ > 0` and `r > 0`, as the lemma requires. The hypotheses are
  the bounds of Proposition 4.1 for the finitely many derivatives `R_{u_i} E`. For `a ∈ A_G^∞`
  and imaginary `λ` they hold at `a g` because they hold at `g` and
  `|R_{u_i} E(λ)(a g)| = |R_{u_i} E(λ)(g)|` (the item on `A_G`; right derivatives commute with
  central translations), while `(1 + ‖H_G(a)‖)^1 ≥ 1`. The conclusion, evaluated at `a = 1`, is
  `|(E − E_Q)(g)| ≤ c e^{(ρ − τ β_Q)(H_0(g))} (1 + ‖H_0(g)‖)^n` for `g ∈ G(𝔸)^1 ∩ 𝔰_G`. The
  item on `A_G` then recovers every `z ∈ A_G`. Hypotheses and conclusion are homogeneous in
  the function: if the inputs hold with constants `M c_i`, the conclusion holds with `M c`.
  Proposition 4.1 gives such an `M` uniformly for `λ` in the compact set `Λ = i e(C)`. All
  `E(φ, λ)` are right invariant under one compact open subgroup `K'_f`, because `φ` is
  `K`-finite. Thus `m = n` depends only on `Λ`, while `B` depends on `t`, `Ω` and `k`.
- **Siegel points.** Lemma 3.1 bounds `φ − φ_P` at points `a g` with `g ∈ 𝔰_G`; here the points
  are `z b ω` with `ω` in an arbitrary compact `Ω`. Apply the lemma to the right translates
  `R_ω E`, `ω ∈ Ω`; constant terms commute with right translation. For `g = n_0 m_0 b' k` in a
  Siegel set, `E(g ω) = E(b' ω')` with `ω'` in a compact set, because conjugation by `b'^{-1}`
  in the positive chamber contracts `N_0(𝔸)` and the compact parts of `𝔰_G` are bounded. So
  Proposition 4.1 (stated for every compact set of right translations) gives the hypotheses
  uniformly in `ω ∈ Ω`, and the conclusion is evaluated at `g = b`. For a threshold `t < 1`
  write `b = b⁺ b⁻` with `b⁺` in the closed positive chamber and `b⁻` in a compact box of
  `A_{T₀}` (for `t ≥ 1` take `b⁻ = 1`). Then `b⁻` commutes with `b⁺` and is absorbed into the
  compact set: `(E − E_Q)(z b ω) = (E − E_Q)(z b⁺ (b⁻ ω))`. On the box the root logarithms
  `log |β(b⁻)|` are bounded by a constant `c₀`, so `log |β(b⁺)|` differs from `log |β(b)|` by at
  most `c₀`. The conditions on `R` and `s` for `b` therefore give those for `b⁺` with `R + c₀`
  and `s − c₀`. Here `(1 + R + c₀)^m ≤ (1 + c₀)^m (1 + R)^m` and
  `e^{−k(s − c₀)} = e^{k c₀} e^{−k s}`. The modulus changes by a bounded positive factor, not
  by a bounded additive amount: it is a character, `δ(b) = δ(b⁺) δ(b⁻)`, and `δ(b⁻)` is bounded
  above and away from zero on the compact box. So `δ(b⁺)^{1/2} ≤ C δ(b)^{1/2}` for a constant
  `C`. All these constants are absorbed into `B`.
- **Root coordinates.** `b ∈ A_{T₀}` lies in the derived group (`IsSiegelAlgebraicSetup`), so
  `X = H_0(b) ∈ 𝔞_0^G`. On `𝔞_0^G` the simple roots form a basis of the dual, and
  `log |β(b)| = d β(X)` for a fixed `d > 0` (the normalization of the idele norm). Hence
  `1 + ‖X‖ ≪ 1 + R` when `|log |β(b)|| ≤ R` for all `β`, and
  `d β_Q(X) = min_{α ∉ J} log |α(b)| ≥ s` when `s ≤ log |α(b)|` for all `α ∉ J` (such an `α`
  exists). For `k ≥ 1`, `τ = k d` gives `e^{−τ β_Q(X)} ≤ e^{−k s}`. For `k = 0` the factor
  `e^{−k s}` is `1`. The chamber threshold gives `d β(X) = log |β(b)| ≥ log t` for every simple
  `β`, so `β_Q(X) ≥ (log t)/d` and `e^{−τ β_Q(X)} ≤ t^{−1/d}`, a constant absorbed into `B`.
  With the best choices of `R` and `s` the right side of the conclusion is
  `B δ(b)^{1/2} (1 + max_β |log |β(b)||)^m e^{−k min_{α ∉ J} log |α(b)|}`.
- **The split component `A_G`.** `z ∈ A_G` is central. For `Re λ` sufficiently regular,
  `E(λ)(z g) = e^{λ(H_G(z))} E(λ)(g)` (each `γ`-term of the series is multiplied by this factor,
  and `δ_P(z) = 1`), hence for all `λ ∈ D` by uniqueness of meromorphic continuation, and
  `E(λ)_Q(z g) = e^{λ(H_G(z))} E(λ)_Q(g)` because `z` commutes with `N_Q(𝔸)`. For imaginary
  `λ` the factor has modulus one, so the left side of the conclusion does not depend on `z`.
  This is why Lemma 3.1 is evaluated at `a = 1`, where its factor `(1 + ‖H_G(a)‖)^r` equals
  `1`, and why its hypotheses with `r = 1` follow from the bounds at `a = 1`.
- **Continuations.** The values `E(i e(x))` are those of the continued Eisenstein series: any
  two continuations agree on the intersection of their domains, by uniqueness of meromorphic
  continuation from the nonempty open regular region
  (`ParabolicRootPresentation.eqOn_of_regularParameter`).
- **Transfers.** The statement quantifies over every presented parabolic `P` with
  `P(𝔸)K = G(𝔸)`, every maximal compact `K` that is also Iwasawa for the minimal parabolic of the
  setup, and every setup. The reduction to Delorme's setting is the one described in
  `AdelicEisensteinWeakConstantTermApproximationStatement.md` ("Transfers"); the constant term
  along `Q` does not involve `K`.

## Scope

The statement asserts neither Lemma 3.1 for general smooth functions nor Proposition 4.1; it
asserts their consequence for the Eisenstein series `E(φ, λ)`, uniformly for `λ ∈ i e(C)`,
without derivatives. `K` is assumed Iwasawa for the minimal parabolic of the setup, as in
`EisensteinWeakConstantTermApproximationStatement`; no Iwasawa property for `Q` is assumed, since
the constant term does not involve `K`. Nothing is proved here.
