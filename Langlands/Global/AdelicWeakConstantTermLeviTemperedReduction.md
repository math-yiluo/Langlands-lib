# Weighted temperedness of weak constant terms from Siegel estimates on the Levi

Module `Langlands.Global.AdelicWeakConstantTermLeviTemperedReduction`, namespace
`Langlands.Global`.

The module states two propositions and proves that together they imply
`WeakConstantTermLeviTemperedStatement` (module
`Langlands.Global.AdelicWeakConstantTermLeviEstimates`):

| Declaration | Kind | Source |
| --- | --- | --- |
| `NormOneSiegelDominatedIntegrabilityStatement` | statement | derived from Delorme (2.5), (2.7)–(2.8), Lemma 2.1, (2.10) and Proposition 3.5 (i) ⇒ (ii); Mœglin–Waldspurger I.2.2 (vii) |
| `WeakConstantTermLeviSiegelBoundStatement` | statement | derived from Delorme Lemma 3.8 (ii), with Definition 3.3, Lemma 3.2 and Proposition 3.5; Mœglin–Waldspurger I.1.4 |
| `weakConstantTermLeviTempered_of_siegel` | theorem | internal |

Neither proposition is proved in this module. The theorem is a reduction:

```lean
theorem weakConstantTermLeviTempered_of_siegel
    (hT : WeakConstantTermLeviSiegelBoundStatement)
    (hI : NormOneSiegelDominatedIntegrabilityStatement) :
    WeakConstantTermLeviTemperedStatement
```

It uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
`WeakConstantTermLeviTemperedStatement` and all notions it uses are unchanged.

## Sources

- P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered
  as `delorme-2023-spectral-theorem-langlands` (published PDF, SHA-256
  `9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`; its numbering and page
  numbers are used):
  - §2, p. 5: `K` is a good maximal compact subgroup of `G(𝔸)` in good position with respect
    to the minimal Levi subgroup `M₀`;
  - §2, p. 7: Siegel domains `𝔰_P = Ω₀ {exp X | X ∈ 𝔞₀, α(X + T) ≥ 0 for α ∈ Δ₀^P} K` of
    `[G]_P` (2.3), the inclusion `𝔰_P ⊆ Ω_{N_P} {exp X | X ∈ 𝔞₀^{+,P}} Ω` with `Ω` compact
    (2.4), and Lapid's bound (2.5), `∫_{P₀(F) \ 𝔰_G} Ξ(g)² σ_L(g)^{-d} dg < ∞`;
  - §2, p. 8: the quotient functions (2.6), the comparison `‖g‖ ≈ ‖g‖_{[G]_P}` on `𝔰_P` (2.7),
    the height `σ(g) = 1 + log ‖g‖` and `σ_{[G]_P} ∼ σ ∼ 1 + ‖H₀‖` on `𝔰_P` (2.8), the
    function `Ξ^{[G]}`, Lemma 2.1 (`Ξ^{[G]} ∼ e^{ρ(H₀)}` and `σ_{[G]} ∼ 1 + ‖H₀‖` on `𝔰_G`)
    and (2.10), `∫_{[G]} (1 + σ_{[G]}(x))^{-d_G} Ξ^{[G]}(x)² dx < ∞`;
  - §3.1, p. 11: Lemma 3.2, for `φ ∈ 𝒜_P(G)` the equivalent conditions a)
    `|φ| ≪ Ξ^{[G]_P} σ_{[G]_P}^d`, b) `|φ(g)| ≪ e^{ρ(H₀(g))} (1 + ‖H₀(g)‖)^d` on every Siegel
    domain `𝔰_P`, c) `|φ(exp X ω)| ≪ e^{ρ(X)} (1 + ‖X‖)^d` for `ω` in every compact
    `Ω ⊆ G(𝔸)` and `X ∈ 𝔞₀^{+,P}`; Definition 3.3, the space `𝒜_P^{temp}(G)`;
  - §3.1, p. 12: Proposition 3.5, `φ` tempered if and only if `[G]`-tempered; the implication
    (i) ⇒ (ii) "follows from the definition of temperedness, especially condition a) in
    Lemma 3.2 and (2.10)";
  - §3.2–3.3, pp. 13–14: Proposition 3.6 (exponents of constant terms of tempered forms are
    subunitary), Definition 3.7 (the weak constant term `φ_P^w`), the transitivity relations
    (3.5)–(3.6) and Lemma 3.8 (ii): `φ_P^w ∈ 𝒜_P^{temp}(G)` for `φ ∈ 𝒜^{temp}(G)`;
  - §3.4, p. 15: the pairing (3.7), absolutely convergent integrals over `[G]¹` and over
    `K × M_P(F) \ M_P(𝔸)¹`.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`:
  - I.1.4, property (ii) and the remark after it (printed pp. 4–5, chapter file
    `05.1_pp_1_18_Hypotheses_and_general_notation.pdf`): after fixing a minimal parabolic `P₀`
    and a Levi subgroup `M₀`, the maximal compact subgroup `K` can be chosen so that
    `P(𝔸) ∩ K = (M(𝔸) ∩ K)(U(𝔸) ∩ K)` and `M(𝔸) ∩ K` is a maximal compact subgroup of `M(𝔸)`
    for every standard parabolic `P = MU`;
  - I.2.2 (vii) (printed pp. 20–21, chapter file
    `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`), points of a Siegel set are
    almost minimal for the height in their `G(F)`-orbit.
- E. Lapid, *On the Harish-Chandra Schwartz space of G(F)\G(A)*, registered as
  `lapid-2013-harish-chandra-schwartz-space-automorphic`, §2, (5): the bound quoted as
  Delorme's (2.5).

## Siegel data

The Siegel data are those of `Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction`, with
the meaning given in its Markdown page. For a group `H` (here `G` or a Levi subgroup `M`), an
algebraic Siegel setup `(T, i, ν, T₀, j)` with `IsSiegelAlgebraicSetup F H T i ν T₀ j`, compact
factors `C`, a threshold `t : ℝ≥0ˣ` and a compact set `Ω ⊆ H(𝔸)`:

- `IsSiegelPoint F H T i ν T₀ j C t Ω a x` says `x = z · (n m a k) · w` with `z ∈ A_H`,
  `n ∈ Ω_N`, `m ∈ Ω_M ⊆ M₀(𝔸)¹`, `a ∈ A_{T₀}` with `|β(a)| ≥ t` for every simple relative
  root `β`, `k` in the compact subgroup of `C`, and `w ∈ Ω`;
- `siegelModulus F H T i ν T₀ j a = ∏_{β > 0} |β(a)|^{m_β} = δ_{P₀}(a)` is the modulus of the
  minimal parabolic of the setup at the torus coordinate, so its square root is
  `e^{ρ₀(H₀(a))}`;
- `adelicLogHeight F H rho x = 1 + log max(1, ‖x‖_ρ)` is Delorme's `σ(x)` at the point `x`,
  and `rationalLogHeight F H rho y = 1 + log max(1, inf_{γ ∈ H(F)} ‖γ x‖_ρ)` for `y = H(F) x`
  is the quotient height `σ_{[H]}`.

## `NormOneSiegelDominatedIntegrabilityStatement`

**Statement.** For a number field `F : Type`, an affine group scheme `G` over `F`, locally of
finite type, with `IsConnectedReductive G`, and a matrix representation
`rho : MatrixRepresentation G (Fin N)` with `IsClosedSubgroup rho`, there exist an algebraic
Siegel setup `(T, i, ν, T₀, j)`, compact factors `C`, a threshold `t` and a compact set
`Ω ⊆ G(𝔸)` such that for every `d : ℕ` there are `n : ℕ` and `B : ℝ≥0` with the following
property. Let `f : G(𝔸) → [0, ∞]` be measurable and left `G(F)`-invariant, with

`f(x) ≤ δ(a) σ(x)^d`

at every point `x` of the Siegel set `A_G · Ω_N Ω_M A_{T₀}(t) K · Ω` that lies in the
norm-one subgroup `G(𝔸)¹` (`normOneSubgroup F G`), for every torus coordinate `a` of `x`. Then

`∫_{G(F) \ G(𝔸)¹} f(y) σ_{[G]}(y)^{-n} dy ≤ B`,

where `f(y)` is evaluated at the chosen representative `Quotient.out y ∈ G(𝔸)¹`, the weight
`σ_{[G]}(y)^{-n}` is `rationalLogHeight` at the image of `y` in `G(F) \ G(𝔸)`
(`normOneQuotientInclusion`), and `dy` is `normOneRationalQuotientHaarMeasure F G`, the quotient
by the discrete subgroup `G(F)` of the Haar measure of `G(𝔸)¹`. The constant `B` does not depend
on `f`.

**Provenance (derived).** The statement is the integration step in the proof of
Proposition 3.5 (i) ⇒ (ii) of Delorme, written on the norm-one quotient `[G]¹` over which
Delorme's pairing (3.7) is taken, with the following changes.

1. *Siegel domination in place of `Ξ`.* Condition a) of Lemma 3.2 bounds `|φ|²` by
   `(Ξ^{[G]})² σ_{[G]}^{2d}`, and by Lemma 2.1 (i), `Ξ^{[G]} ∼ e^{ρ(H₀)}` on Siegel domains. The
   statement takes the Siegel form: `f` plays the role of `|φ|²`, and `δ(a) = e^{2ρ₀(H₀(a))}`
   that of `(Ξ^{[G]})²`. By (2.4) every Siegel domain of Delorme is of the form used here, up
   to compact factors.
2. *The two heights.* The hypothesis uses `σ(x)` of the point and the conclusion the quotient
   height `σ_{[G]}`. Since `σ_{[G]}(G(F) x) ≤ σ(x)` (the Library's `rationalLogHeight_mk_le`),
   a bound in terms of `σ_{[G]}` would imply the stated hypothesis. Conversely, on Siegel sets
   the two heights are comparable by (2.7)–(2.8), the property (vii) of Mœglin–Waldspurger
   I.2.2, proved in the Library for weak Siegel products as
   `AdelicSiegelFactors.siegelNormMinimalityStatement`. This comparison is what turns the
   weight `σ_{[G]}^{-n}` into decay along the Siegel set.
3. *The weight.* (2.10) has the weight `(1 + σ_{[G]})^{-d_G}`; since `σ_{[G]} ≥ 1`
   (`one_le_rationalLogHeight`), `σ_{[G]}^{-n}` with `n ≥ d_G` is at most `2^{d_G}` times it.
   The statement asks for some `n` for every growth exponent `d`, which is what (2.10) gives
   after absorbing the factor `σ^d`.
4. *Choice of the Siegel set and uniformity.* As in the Library's
   `SiegelDominatedIntegrabilityStatement` (on `[G]`, module
   `AdelicWavePacketRapidDecaySiegelReduction`), the Siegel data are existentially quantified:
   they must be chosen so that the Siegel set covers `G(𝔸)¹` modulo `G(F)`. The bound `B` is
   uniform in `f`; a family of functions with a common Siegel bound therefore has uniformly
   bounded integrals, which is used below for the integral over `K`.

The following route is explanatory and is not proved in this module. The Library proves a
Siegel cover of `G(𝔸)¹` (`AdelicSiegelFactors.adelicSiegelReduction`, module
`AdelicGoodSiegelReductionProof`). On the covering weak Siegel product, norm minimality gives
`σ(x) ≤ c σ_{[G]}(G(F) x)`, so `f(x) σ_{[G]}^{-n} ≤ c^n δ(a) σ(x)^{d-n}`. Unfolding the quotient
integral onto the Siegel set, the Haar density `δ(a)^{-1}` in the Siegel coordinates cancels
`δ(a)`, and the lower bound `σ(n m a k) ≳ 1 + ‖log a‖` makes `σ^{d-n}` integrable over the
chamber for `n` large. The Library's proof of `SiegelDominatedIntegrabilityStatement`
(`siegelDominatedIntegrability`, module `AdelicSiegelDominatedIntegrabilityProof`) carries out
the measure estimates on `[G]` with the weight in the hypothesis.

## `WeakConstantTermLeviSiegelBoundStatement`

**Statement.** The hypotheses up to the weak constant term are those of
`WeakConstantTermLeviTemperedStatement`, in the same order: a number field `F`, a connected
reductive `G`, a maximal compact subgroup `K ⊆ G(𝔸)`, a closed matrix embedding `rho`,
`hsmooth`, `hcalc`, a compatible family `𝓕` of standard parabolics with
`IsIwasawaCompact (𝓕.p 𝓕.bot) K`, a log-square-integrable automorphic form `Φ`
(`IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ`), a standard index `J` and a
weak constant term `ψ` of `Φ` along `P = P_J`
(`𝓕.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J Φ ψ`). Write
`M = 𝓕.M J` and `ι = map F M G (𝓕.l J ≫ 𝓕.p J)` for the Levi embedding `M → P → G`. Then for
every algebraic Siegel setup `(T, i, ν, T₀, j)` of `M`, all compact factors `C`, thresholds
`t`, compact sets `Ω ⊆ M(𝔸)` and compact sets `Ω' ⊆ G(𝔸)` there are `e : ℕ` and `B : ℝ` with

`|ψ(ι(m) w)| ≤ B · δ_M(a)^{1/2} · σ_M(m)^e`

for every `m ∈ M(𝔸)¹` with `IsSiegelPoint F M T i ν T₀ j C t Ω a m` and every `w ∈ Ω'`. Here
`δ_M = siegelModulus F M T i ν T₀ j` and `σ_M = adelicLogHeight F M (rho.restrict (𝓕.l J ≫ 𝓕.p J))`,
the height of `M` for the restriction of `rho` along `M → P → G`.

**Correspondence with Delorme (provenance derived).** Lemma 3.8 (ii) is stated for
`φ ∈ 𝒜^{temp}(G)`, with `K` a good maximal compact subgroup of `G(𝔸)` in good position with
respect to the minimal Levi subgroup `M₀` (§2, p. 5). The hypotheses of the statement are weaker
in two respects: `Φ` is only weighted square-integrable (`IsLogSquareIntegrableAutomorphicForm`
bounds `Φ` itself, not its derivatives), and `K` is any maximal compact subgroup with
`P_∅(𝔸) K = G(𝔸)`. The statement follows from Lemma 3.8 (ii) in three steps. Steps 1 and 2
bring `Φ` and `ψ` into Delorme's setting and are not part of Delorme's lemma.

*Step 1: change of the compact subgroup.* `K` enters the hypotheses through its archimedean
part `K_∞ = K.comap (ofInfinite F G)`, in two places:

- the automorphy condition `IsAutomorphicFunctionOn … (K.comap (ofInfinite F G)) … Φ` inside
  `IsLogSquareIntegrableAutomorphicForm` (module
  `Langlands.Global.AdelicWavePacketCompletenessReduction`) asks that the right translates of
  `Φ` by `K_∞` span a finite-dimensional space;
- `𝓕.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J Φ ψ` (module
  `Langlands.Global.AdelicTemperedVanishingReduction`) asks for a decomposition (3.2) of the
  constant term of `Φ` whose components `c λ` are automorphic on `U(𝔸) M(F) \ G(𝔸)` with the
  same `K_∞`-finiteness (`IsAutomorphicExponentDecomposition`).

Otherwise `K` enters only through the hypotheses that it is maximal compact and that
`P_∅(𝔸) K = G(𝔸)`. The finite part of `K` plays no role, since smoothness at the finite places
is right invariance under an open subgroup of `G(𝔸_f)`. The Iwasawa condition alone does not
give the compact subgroup of `M(𝔸)` used in Delorme's proof. For instance, in `GL₃(ℝ)` let
`u = I + E₁₃`. The conjugate `u O(3) u⁻¹` still satisfies `B(ℝ) u O(3) u⁻¹ = GL₃(ℝ)` for the
upper triangular Borel subgroup `B`. But it meets the block Levi subgroup `GL₂(ℝ) × GL₁(ℝ)` only
in the finite group of diagonal sign matrices whose first and third entries agree, while the
compact subgroup in good position gives `O(2) × O(1)`.

The reduction to good position is a right translation. Let `K₀` be a maximal compact subgroup
of `G(𝔸)` in good position with respect to the minimal Levi subgroup `M₀` of `𝓕`
(Mœglin–Waldspurger I.1.4 (ii): `K₀` can be chosen with
`P(𝔸) ∩ K₀ = (M(𝔸) ∩ K₀)(U(𝔸) ∩ K₀)` and `M(𝔸) ∩ K₀` maximal compact in `M(𝔸)` for every
standard parabolic `P = MU`). The archimedean
parts `K_∞` and `K₀,∞` are maximal compact subgroups of `G(F_∞)`
(`IsMaximalCompactSubgroup.isMaximalCompact_comap_ofInfinite`). So
`InfiniteAdelicGroupPoints.infiniteAdelicMaximalCompactConjugacy` gives `b ∈ G(F_∞)` with
`b K_∞ b⁻¹ = K₀,∞`. Put `τ = ofInfinite F G b`, `Φ_τ(g) = Φ(g τ)` and `ψ_τ(g) = ψ(g τ)`.

- By `adelicWeakConstantTermRightTranslation` (module
  `Langlands.Global.AdelicWeakConstantTermRightTranslation`), `Φ_τ` satisfies
  `IsLogSquareIntegrableAutomorphicForm` for `K' = τ K τ⁻¹`, with the same weight exponent. In
  addition, `ψ_τ` is a weak constant term of `Φ_τ` along `P` for the archimedean part of `K'`.
  That archimedean part is `b K_∞ b⁻¹ = K₀,∞`.
- `K'` is maximal compact (`IsMaximalCompactSubgroup.map_conj`), and `P_∅(𝔸) K' = G(𝔸)`
  (`IsIwasawaCompact.conjInv`), so `Φ_τ` and `K'` satisfy all hypotheses of the statement.
- `Φ_τ` and the components of `ψ_τ` are `K₀,∞`-finite. They are also `K₀`-finite at the finite
  places, being fixed by open subgroups of `G(𝔸_f)`. The decomposition (3.2) into components
  with distinct exponents is unique, so `ψ_τ` is Delorme's `(Φ_τ)_P^w`, now for the compact
  subgroup `K₀`.
- The conclusion for `ψ` follows from the conclusion for `ψ_τ`. Indeed
  `ψ(ι(m) w) = ψ_τ(ι(m) w τ⁻¹)`, and `Ω' τ⁻¹` is compact, so the bound for `ψ_τ` on `Ω' τ⁻¹`
  is the bound for `ψ` on `Ω'`, with the same `e` and `B`.

*Step 2: temperedness of `Φ_τ`.* Lemma 3.8 (ii) assumes `φ ∈ 𝒜^{temp}(G)`. By Definition 3.3
this means that `φ` and all its derivatives `R_u φ`, `u ∈ U(𝔤_∞)`, satisfy the conditions of
Lemma 3.2 with a common `d`. By Proposition 3.5 this is `[G]`-temperedness, a weighted `L²`
condition on every `R_u φ`. `IsLogSquareIntegrableAutomorphicForm` controls only `Φ`. The
needed bridge is the proposition `LogSquareIntegrableSiegelDerivativeBoundsStatement` (module
`Langlands.Global.AdelicLogSquareIntegrableSiegelDerivativeBounds`, which states it and does
not prove it). Its hypotheses are those of the present statement up to `Φ`, for every maximal
compact `K` with `P_∅(𝔸) K = G(𝔸)`. Its conclusion bounds every derivative
`R(X₁) ⋯ R(X_r) Φ` by `C_D δ_{P₀}(a)^{1/2} σ(x)^m` on every Siegel set of `G`, with `m` common
to all words. By (2.4) this is condition c) of Lemma 3.2 for `P = G`, for `Φ` and all its
derivatives, that is `Φ ∈ 𝒜^{temp}(G)` by Definition 3.3. The paired Markdown of that module
describes a route: Harish-Chandra's reproducing kernel `Φ = Φ * α` and the comparison of
heights under compact right translation put every `R_u Φ` in the weighted `L²` space of `Φ`,
and Proposition 3.5 (ii) ⇒ (i) then gives the pointwise bounds. Applied to `Φ_τ` and `K'`,
whose hypotheses hold by Step 1, it gives `Φ_τ ∈ 𝒜^{temp}(G)`. This proposition is an input
to the proof of the present statement, separate from Lemma 3.8.

*Step 3: Lemma 3.8 (ii) on Siegel sets of `M`.* Lemma 3.8 (ii), for `Φ_τ` and `K₀`, says that
`ψ_τ = (Φ_τ)_P^w` lies in `𝒜_P^{temp}(G)`. So by Definition 3.3 and Lemma 3.2 c) there is `d`
with `|ψ_τ(exp X ω)| ≪ e^{ρ(X)} (1 + ‖X‖)^d` for `X ∈ 𝔞₀^{+,P}` and `ω` in any compact subset
of `G(𝔸)`. The statement is this bound on the norm-one Siegel sets of `M`, translated on the
right by a compact set (by Step 1, the compact set `Ω' τ⁻¹` for `ψ_τ`):

1. *Siegel points of `M`.* Let `m = z (n m₀ a k) w_M` be a norm-one Siegel point of `M`. The
   factors `n`, `m₀`, `k`, `w_M` lie in compact sets; since `m` and `n m₀ a k` have norm one, so
   does `z w_M`, and `z` lies in a compact subset of `A_M`. The point `m₀` commutes with `a`,
   and `a⁻¹ n a` stays in a compact set because `|β(a)| ≥ t` for the simple roots of `M`. So
   `ι(m) w = exp(X) ω` with `X = H(a)` in a translate of the positive chamber of `M` and `ω` in a
   compact subset of `G(𝔸)`, as in (2.4).
2. *The modulus.* `a` lies in a maximal split torus of the derived group of `M`. There `ρ_P`
   vanishes, so `e^{ρ(X)} = e^{ρ^M(X)} = δ_M(a)^{1/2}`, the half modulus of the minimal
   parabolic of `M` given by the setup.
3. *The logarithmic factor.* With the other factors in compact sets, `1 + ‖X‖` is bounded by a
   constant times `σ_M(m)`, so `(1 + ‖X‖)^d` is represented by a power of `σ_M(m)`.
4. *Setups of `M`.* Delorme works with the Siegel domains of the fixed minimal parabolic
   `P₀ ∩ M`. Every algebraic Siegel setup of `M` is conjugate to one adapted to `P₀ ∩ M` by a
   rational point of `M`, and `ψ` is left invariant under `M(F)` (it is automorphic on
   `U(𝔸) M(F) \ G(𝔸)`), so the bound for one class of Siegel sets gives the bound for all of
   them after enlarging the compact factors. The statement quantifies over all setups, as
   `LogSquareIntegrableSiegelDerivativeBoundsStatement` does for `G`.
5. *Derivatives.* Definition 3.3 also bounds the derivatives of `ψ`; only the bound on `ψ`
   itself is stated.

Delorme's proof of Lemma 3.8 (ii), read for `Φ_τ` and `K₀`, runs as follows. Proposition 3.6
applied to `Φ_τ` (the exponents of the constant terms of a tempered form are subunitary) and
the relations (3.6) show that the exponents of the normalized restrictions
`((Φ_τ)_P^w)_{k, M_P}`, `k ∈ K₀`, along the standard parabolics of `M_P` are subunitary. These
restrictions are automorphic forms on `M_P` for the maximal compact subgroup `M_P(𝔸) ∩ K₀` of
`M_P(𝔸)`, which is in good position. The converse direction of Proposition 3.6 on `M_P`
(Delorme cites Mœglin–Waldspurger, Lemma I.4.1) gives their temperedness on `M_P`.
`K₀`-finiteness gives uniformity in `k ∈ K₀`. Finally, every compact subset of `G(𝔸)` lies in
a set `N_P(𝔸) Ω_M K₀` with `Ω_M ⊆ M_P(𝔸)` compact, because `P(𝔸) K₀ = G(𝔸)`. The step on
`M_P` uses the good position of `K₀`, which is why Step 1 precedes it.

## Proof of `weakConstantTermLeviTempered_of_siegel`

Fix the data of `WeakConstantTermLeviTemperedStatement`, the weak constant term `ψ` and a point
`x` of the positive split component `𝔄_P`, and write `y` for its image in `G(𝔸)`. Let `M`, `ι`
and `σ_{[M]} = rationalLogHeight F M (rho.restrict (𝓕.l J ≫ 𝓕.p J))` be as above.

1. **The Levi.** `M` is connected reductive (`(𝓕.isCompatible J).levi.isConnectedReductive`),
   and `rho.restrict (𝓕.l J ≫ 𝓕.p J) = (𝓕.l J ≫ 𝓕.p J) ≫ rho` is a closed embedding, being a
   composite of closed immersions. `NormOneSiegelDominatedIntegrabilityStatement` for `M` gives
   Siegel data `(T, i, ν, T₀, j, C, t, Ω)` of `M` and, for every `d`, an exponent `n` and a bound.
2. **Properties of `ψ`.** By definition of `IsWeakConstantTerm`, `ψ` is the sum of the
   components `c λ` with unitary `λ` of a decomposition of the constant term of `Φ`. Each `c λ`
   is automorphic on `U(𝔸) M(F) \ G(𝔸)`, hence continuous and left invariant under
   `parabolicQuotientSubgroup`; so is the finite sum `ψ`.
3. **Commutation.** `y ι(m) = ι(m) y` for every `m ∈ M(𝔸)`
   (`StandardParabolicFamily.commute_positiveSplitComponent_levi`). With the invariance under
   `ι(M(F))` this gives `ψ(y ι(γ m) g) = ψ(y ι(m) g)` for rational `γ`.
4. **The Siegel bound.** `K` is compact, so `Ω' = y K` is compact.
   `WeakConstantTermLeviSiegelBoundStatement` with the Siegel data of step 1 and `Ω'` gives `e`
   and `B`. Step 1 with `d = 2e` gives `n` and a bound `C₀`; this `n` is the exponent of the
   conclusion. Put `B' = max(B, 1)`.
5. **One `k` at a time.** For `k ∈ K` let `f_k(m) = |ψ(y ι(m) k)|² / B'²` on `M(𝔸)`. It is
   measurable (continuous) and left `M(F)`-invariant (step 3). At a norm-one Siegel point `m`
   of `M` with torus coordinate `a`, step 3 gives `ψ(y ι(m) k) = ψ(ι(m) (y k))` with
   `y k ∈ Ω'`, so step 4 gives `|ψ(y ι(m) k)| ≤ B' δ_M(a)^{1/2} σ_M(m)^e` (`δ_M ≥ 0`, as a
   finite product of nonnegative reals), that is `f_k(m) ≤ δ_M(a) σ_M(m)^{2e}`. Hence
   `∫_{[M]¹} f_k σ_{[M]}^{-n} ≤ C₀`. Since `σ_{[M]} ≥ 1`, `σ_{[M]}^{-2n} ≤ σ_{[M]}^{-n}`, and
   therefore `∫_{[M]¹} |ψ(y ι(m) k)|² σ_{[M]}(m)^{-2n} dm ≤ B'² C₀`.
6. **The integral over `K`.** The integrand of the conclusion is
   `h(k, q) = ψ(y ι(q̃) k) / σ_{[M]}(q)^n` with `q̃ = Quotient.out q`. Its numerator is
   continuous on `K × M(F) \ M(𝔸)¹`, being the descent of the continuous function
   `(k, m) ↦ ψ(y ι(m) k)`, which is left invariant under the rational points of `M(𝔸)¹`
   (`InducedInnerProductSesquilinear.continuous_prod_out`). The denominator is measurable
   (`measurable_rationalLogHeight` and the continuity of `normOneQuotientInclusion`) and
   nonzero. So `h` is almost everywhere strongly measurable. By `lintegral_prod_le` and step 5,
   `∫_{K × [M]¹} |h|² ≤ ∫_K B'² C₀ dk = B'² C₀ < ∞`, the Haar measure of `K` being a
   probability. By `memLp_two_iff_integrable_sq_norm`, `h ∈ L²` for
   `𝓕.squareIntegrablePairingMeasure K hK.isCompact J`.
