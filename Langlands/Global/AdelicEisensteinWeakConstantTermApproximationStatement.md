# Approximation of Eisenstein series by their weak constant terms on cones

Module `Langlands.Global.AdelicEisensteinWeakConstantTermApproximationStatement`, namespace
`Langlands.Global`. It states one proposition, `EisensteinWeakConstantTermApproximationStatement`,
and proves nothing.

## Source

P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered as
`delorme-2023-spectral-theorem-langlands` (published PDF numbering).

- §4.1, pp.16–17. (4.1): the relative Eisenstein series `E^Q_P(·, φ, λ)` for standard
  `P ⊆ Q`, characterized by `E^Q_P(·, φ, λ)^{M_Q, k} = E_{P ∩ M_Q}(·, φ^{M_Q, k}, λ)`. (4.3): for
  `λ ∈ i𝔞_P^*` the weak constant term of `E_P(·, φ, λ)` along `Q` is
  `∑_{s ∈ W(P, Q)} E^Q_{Q_s}(·, M(s, λ) φ, s λ)`, holomorphic in a neighborhood of `i𝔞_P^*`. The
  operators `M(s, λ)` are meromorphic on a finite-dimensional subspace of `A^2_P` (p.16).
- The holomorphy used in (4.1) and (4.3) comes from E. Lapid, *On Arthur's asymptotic inner
  product formula of truncated Eisenstein series* (Clay Math. Proc. 13, 2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`. Its Proposition 6 (printed
  pp.329–330) gives holomorphy of Eisenstein series of square-integrable data at imaginary
  parameters, which applies to the Levi series in (4.1). Its Working Hypothesis is supplied by
  the continuation of Bernstein–Lapid 2024 (Theorem 2.3 and the Corollary at the end of §8.6,
  p.226). The paragraph after the Working Hypothesis (printed p.312) gives holomorphy of the
  normalized intertwining operators at unitary parameters.
- §4.2, p.17: Proposition 4.1 (uniform temperedness: `E_P(·, φ, λ) ∈ ℱ_{Λ, ρ, n}` of (4.5) for
  `Λ ⊆ i𝔞_P^*` compact).
- §5.1, p.19: Lemma 5.3. For `Ω ⊆ G(𝔸)` compact, `δ > 0`, `Λ ⊆ i𝔞_P^*` bounded and
  `φ ∈ A^2_P` there is `ε > 0` with
  `|E_P(n_Q exp X ω, φ, λ) − E_P(n_Q exp X ω, φ, λ)^w_Q| ≪ e^{ρ(X) − ε‖X‖}` for `n_Q ∈ N_Q(𝔸)`,
  `X ∈ 𝔞^{G+}_{0,Q,δ}`, `ω ∈ Ω`, `λ ∈ Λ`. Here
  `𝔞^{G+}_{0,Q,δ} = {X ∈ 𝔞_0^{G+} : α(X) ≥ δ‖X‖ for α ∈ Δ_{P_0} \ Δ^Q_{P_0}}` (Lemma 5.2).
- §5.2, pp.20–21: the proof of Proposition 5.4 splits `E = (E − E^w_Q) + E^w_Q` on such cones
  and uses Lemma 5.3 and (4.3).

## The statement

The data are:

- a number field `F : Type` and a connected reductive `G` over `F`;
- a parabolic `p : P → G` with presentation `r : ParabolicRootPresentation p l a` and geometric
  unipotent radical `iU`;
- a maximal compact subgroup `K` of `G(𝔸)` with `hK : IsIwasawaCompact p K`;
- a closed matrix embedding `rho` of `G`, and `hsmooth`, `hcalc`;
- `φ ∈ A^2_P` (`IsSquareIntegrableInducedForm`);
- `E : X^*(P) ⊗ ℂ → G(𝔸) → ℂ` and `D` such that `D` contains the imaginary parameters, every
  `λ ↦ E λ g` is meromorphic in linear coordinates with domain of holomorphy `D`, and
  `E λ = hK.eisensteinSeries φ λ` for `Re λ` sufficiently regular.

In addition:

- real linear coordinates `e : ℝⁿ ≃ X^*(P) ⊗ ℝ` and a compact `C ⊆ ℝⁿ`;
- an algebraic Siegel setup `(T, i, ν, T₀, j)` (`IsSiegelAlgebraicSetup`) such that `K` is an
  Iwasawa subgroup for its standard minimal parabolic `Standard.parabolicHom i ν ∅`;
- a subset `J` of the simple roots `Δ = simpleRelativeRoots i ν` with `J ≠ Δ`, its standard
  parabolic `Q = Standard.parabolicScheme i ν J`, and `hKQ : IsIwasawaCompact
  (Standard.parabolicHom i ν J) K`, whose Iwasawa height `H_Q` defines
  `m_Q(g)^λ = hKQ.heightPower λ g = exp ⟨λ, H_Q(g)⟩`;
- `δ > 0`, a threshold `t : ℝ≥0ˣ` and a compact `Ω ⊆ G(𝔸)`.

Write `|β(b)|` for the idele norm of `β(b)` at a point `b` of the positive torus `A_{T₀}`, so
that `logNormHom F T₀ b (j ≫ β) = log |β(b)|`. Write `δ(b) = siegelModulus(b)` and
`σ = adelicLogHeight` (`Langlands/Global/AdelicWavePacketRapidDecaySiegelReduction.lean`).

Conclusion: there are `ε > 0`, `m : ℕ`, `B`, `k : ℕ` and for each `q < k` a function
`c_q : ℝⁿ → ℂ`, a real subspace `V_q ⊆ ℝⁿ`, a real linear map
`L_q : V_q → X^*(Q) ⊗ ℝ` and a function `Φ_q : ℝⁿ → G(𝔸) → ℂ`, such that

1. `ε > 0`;
2. each `c_q` is smooth;
3. each `L_q` is surjective;
4. `Φ_q(x + v, g) = m_Q(g)^{i L_q(v)} Φ_q(x, g)` for `v ∈ V_q`, `x ∈ ℝⁿ`, `g ∈ G(𝔸)`, where
   `i L_q(v) = imaginaryParameter (L_q v)`;
5. `x ↦ Φ_q(x, g)` is continuous for every `g`;
6. `‖Φ_q(x, z b ω)‖ ≤ B · δ(b)^{1/2} · σ(z b ω)^m` for `x ∈ C`, `z ∈ A_G`
   (`RestrictionSplitCentre.canonicalSubgroup F G`), `b` in the weak simple-root chamber
   `|β(b)| ≥ t` (`PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t`, mapped to `G(𝔸)` by
   `positiveMap`) and `ω ∈ Ω`;
7. `‖E(i e(x))(z b ω) − ∑_q c_q(x) Φ_q(x, z b ω)‖ ≤ B · δ(b)^{1/2} · e^{−ε R}` for the same
   `x, z, b, ω` and every real `R` with `|log |β(b)|| ≤ R` for all `β ∈ Δ` and
   `δ R ≤ log |α(b)|` for all `α ∈ Δ \ J`.

## Correspondence with the source

Take first `P` standard (containing the minimal parabolic of the setup) and `K` in good position,
as in Delorme.

- **The functions `Φ_q` and `c_q`.** For each `s ∈ W(P, Q)` let `Q_s ⊆ Q` be the standard
  parabolic of (4.3), so that `λ ↦ s λ` is a linear isomorphism `𝔞_P^* → 𝔞_{Q_s}^*`. The vectors
  `M(s, λ) φ`, `λ ∈ i𝔞_P^*`, lie in one finite-dimensional subspace of `A^2_{Q_s}` (fixed
  `K`-type and fixed infinitesimal character of `M_{Q_s}`); choose a basis `ψ_{s,l}` and write
  `M(s, λ) φ = ∑_l m_{s,l}(λ) ψ_{s,l}`. The coefficients are holomorphic in a neighborhood of
  `i𝔞_P^*`. The index `q` runs over the pairs `(s, l)`, with
  `c_q(x) = m_{s,l}(i e(x))` and `Φ_q(x, g) = E^Q_{Q_s}(g, ψ_{s,l}, s i e(x))`, the value of
  the relative Eisenstein series, which is analytic on the imaginary axis. Then
  `∑_q c_q(x) Φ_q(x, ·)` is the weak constant term `E_P(·, φ, i e(x))^w_Q` of (4.3), and item 5
  holds.
- **Item 4.** The restriction of characters `X^*(Q) → X^*(Q_s)` is injective; let `𝔞_Q^*`
  denote the image of its real extension in `𝔞_{Q_s}^*`. For `ν ∈ X^*(Q) ⊗ ℂ` the relative
  series satisfies `E^Q_{Q_s}(g, ψ, μ + ν) = m_Q(g)^ν E^Q_{Q_s}(g, ψ, μ)`: each term of the sum
  over `Q_s(F) \ Q(F)` is multiplied by `m_{Q_s}(γ g)^ν = m_Q(γ g)^ν = m_Q(g)^ν`, since `H_Q` is
  the projection of `H_{Q_s}` and is left `Q(F)`-invariant. This holds where the series
  converges and, by uniqueness of meromorphic continuation, for the continuation. Take
  `V_q = {v : s e(v) ∈ 𝔞_Q^*}` and `L_q(v)` the character parameter of `Q` restricting to
  `s e(v)`. `L_q` is surjective because `λ ↦ s λ` is onto `𝔞_{Q_s}^* ⊇ 𝔞_Q^*`. The shift law
  concerns the `Φ_q` only: the coefficients `c_q` are required to be smooth and may vary along
  `V_q`. (The normalized intertwining operators are invariant under shifts by ambient characters
  of `G`; Bernstein–Lapid 2024, §8.6, pp.225–226, describes their dependence on the root
  coordinates for elementary symmetries. No such property is used or asserted here.)
- **Item 6** is Proposition 4.1 for the Levi subgroup `M_Q`, transported to `G(𝔸)` by (4.1).
  Write `ω = n m k` with `n ∈ N_Q(𝔸)`, `m` in a compact subset of `M_Q(𝔸)` and `k ∈ K`. Since
  `E^Q` is left `N_Q(𝔸)`-invariant and `z b` normalizes `N_Q(𝔸)`, `Φ_q(x, z b ω) = Φ_q(x, z b m k)`.
  For `X = H_0(z b) = X_Q + X^Q` with `X_Q ∈ 𝔞_Q` and `X^Q ∈ 𝔞_0^Q`, the equivariance of `ψ_{s,l}`
  gives the factor `e^{ρ_Q(X_Q)}` (`ρ_{Q_s}` restricts to `ρ_Q` on `𝔞_Q`, and `s i e(x)` is
  imaginary). Proposition 4.1 for `M_Q` bounds the rest by `(1 + ‖X^Q‖)^n e^{ρ^Q(X^Q)}`,
  uniformly in `x ∈ C` and in `k` by `K`-finiteness; `X^Q` lies in the `M_Q`-chamber shifted by
  the threshold. Since `e^{ρ_Q(X_Q) + ρ^Q(X^Q)} = e^{ρ(X)} = δ(b)^{1/2}` and `z ∈ A_G` contributes
  no modulus, this is item 6 once `1 + ‖X‖ ≪ σ(z b ω)`, with the additive `1` as in Delorme
  (2.8). For that comparison, diagonalize the restriction of `rho` to the split torus by a fixed
  change of basis. At each archimedean place, the absolute value of each weight at `z b` and its
  inverse is then at most a fixed multiple of the local maximum of the matrix entries of
  `rho(z b)` and of its inverse (the local norms of `RepresentationGrowth.adelicSourceNorm`
  include the entries of the inverse). Taking logarithms costs a fixed additive constant;
  summing over the places with their multiplicities and using that the weights span the real
  character space of the torus bounds `‖X‖` by a constant times
  `1 + log max(1, adelicSourceNorm(z b))`. A bound by the logarithm alone fails near the
  identity: for a conjugated embedding of `SL₂` the logarithm of the raw height is quadratic in
  `‖X‖` there. Finally, right translation by the compact `Ω` changes `σ` by a bounded amount, by
  submultiplicativity of the scaled height `adelicHeight` (`RepresentationGrowth.adelicHeight_mul_le`)
  applied to `ω` and `ω⁻¹`.
- **Item 7** is Lemma 5.3 with `n_Q = 1`.
  - `b ∈ A_{T₀}` lies in the derived group, so `X = H_0(b) ∈ 𝔞_0^G`. On `𝔞_0^G` the simple
    roots form a basis of the dual, so `max_β |β(X)|` is a norm, and
    `log |β(b)| = d β(X)` for a fixed `d > 0` (the normalization of the idele norm).
  - If `|log |β(b)|| ≤ R` for all `β ∈ Δ` and `δ R ≤ log |α(b)|` for `α ∉ J` (such an `α`
    exists), then `‖X‖ ≪ R` and `α(X) ≥ (δ/d) R`, so `α(X) ≥ δ'‖X‖` for a fixed `δ' > 0`, and
    `‖X‖ ≥ c R` because `α(X) ≪ ‖X‖`. Hence `e^{ρ(X) − ε‖X‖} ≤ δ(b)^{1/2} e^{−ε c R}`.
  - For a threshold `t < 1`, write `X = X⁺ + X⁻` with `β(X⁻) = min(β(X), 0)`: `X⁺ ∈ 𝔞_0^{G+}`
    and `X⁻` lies in a compact box. The box element commutes with `b`, is absorbed into `Ω`,
    and changes `δ(b)` by a bounded factor. The cone condition passes to `X⁺` with a smaller
    `δ'` once `‖X⁺‖` is large; on the remaining bounded set of `X⁺` both terms are bounded by
    continuity.
  - `z ∈ A_G` is central. `E(·, λ)` and every term of `E^w_Q` transform under `A_G` by the
    same unitary character `e^{λ(H_G(z))}` (each `s ∈ W(P, Q)` fixes `𝔞_G`), so the left side of
    item 7 does not depend on `z`.
- **Continuations.** The values `E(i e(x))` are those of the continued Eisenstein series: any
  two continuations agree on the intersection of their domains, by uniqueness of meromorphic
  continuation from the nonempty open regular region
  (`ParabolicRootPresentation.eqOn_of_regularParameter`).
- **Transfers.** The statement quantifies over every presented parabolic `P` with
  `P(𝔸)K = G(𝔸)`, every maximal compact `K` that is also Iwasawa for the minimal parabolic of
  the setup, and every setup. The reduction to Delorme's setting uses rational conjugation of
  `P` into standard position, the comparison of compact subgroups (described in
  `AdelicWavePacketCompletenessReduction.md`, "Non-standard parabolics", and in
  `AdelicEisensteinConvergenceStatement.md`), and the `G(F)`-conjugacy of pairs (minimal
  parabolic, maximal split torus). In item 4 the height `H_Q` is that of the given `K`; for a
  non-standard `P` the relative series are formed for the conjugated parabolics with the same
  `K`, which is Iwasawa for every parabolic containing a conjugate of the minimal parabolic
  (`IsIwasawaCompact.of_conjugate_map`, `IsIwasawaCompact.of_comp`). These transfers are part of
  the proof obligation.

## Scope

The statement does not assert the formula (4.3) itself, the holomorphy of `M(s, λ)` or the
derivative estimates of Delorme; it asserts the existence of a decomposition with items 1–7. It
does not identify `∑_q c_q Φ_q` with the weak constant term: the weak constant term of (4.3) is
one admissible choice, and other sums may satisfy items 1–7 (for empty `Ω` the two bounds,
items 6 and 7, are vacuous, so any family satisfying items 1–5, for instance the empty family,
is admissible).
`K` is assumed Iwasawa for the minimal parabolic of the setup and for `Q`. Nothing is proved
here.
