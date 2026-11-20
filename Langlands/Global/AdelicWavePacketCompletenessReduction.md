# Reduction of the completeness of wave packets to four ingredients

Module `Langlands.Global.AdelicWavePacketCompletenessReduction` splits Delorme's proof of the
completeness of wave packets, the published `Langlands.Global.WavePacketCompletenessStatement`,
into four propositions. It proves that the four together imply that statement. It proves none of
the four. In short:

- `SpectralWitnessStatement`: let `W` be a family of rapidly decreasing functions whose
  orthogonal complement in `L²([G])` is stable under right translation by `G(𝔸)`. A nonzero
  `f ∈ L²([G])` orthogonal to `W` yields a nonzero automorphic form with a unitary
  `A_G`-character and moderate weighted-`L²` growth, orthogonal to `W`.
- `WavePacketRapidDecayStatement`: the wave packets of the target are rapidly decreasing.
- `WavePacketOrthogonalTranslationStatement`: the orthogonal complement of the wave packets of
  the target is stable under right translation by `G(𝔸)`.
- `TemperedWavePacketVanishingStatement`: an automorphic form of that kind orthogonal to all
  wave packets of the target is zero.

| Declaration | Kind | Source |
| --- | --- | --- |
| `rationalLogHeight` | definition | Delorme (2.6), `σ` after (2.7); Beuzart-Plessis A.1; MW I.2.2 |
| `IsWavePacket` | definition | the hypothesis of `WavePacketCompletenessStatement` |
| `IsLogSquareIntegrableAutomorphicForm` | definition | Delorme p.12 and Proposition 3.5, Lemma 7.10 |
| `SpectralWitnessStatement` | statement | Delorme Lemma 7.10 and the remark before it; Bernstein 1988 §3 |
| `WavePacketRapidDecayStatement` | statement | Delorme Proposition 5.4 and (2.10) |
| `WavePacketOrthogonalTranslationStatement` | statement | Delorme Theorem 6.1 (Lapid 2011 Theorem 2) and Lemma 6.2; Arthur 2005 Theorem 7.2 |
| `TemperedWavePacketVanishingStatement` | statement | Delorme Theorem 7.1, Proposition 7.8, Lemma 7.11, end of Theorem 7.9, Lemma 3.10 (ii) |
| `wavePacketCompleteness_of_reduction` | theorem (proved) | Delorme, structure of the proof of Theorem 7.9 |

## Sources

- P. Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023)
  109107, registered as `delorme-2023-spectral-theorem-langlands`. The folder holds the published
  PDF and the arXiv TeX 2006.12893; the numbering below is that of the published PDF, whose page
  numbers are the PDF page numbers:
  - §2, p.8: (2.6) `f_{[G]_P}(g) = inf_{γ ∈ M_P(F) N_P(𝔸)} f(γ g)`, "We fix a norm `‖.‖` on
    `G(𝔸)` as in [7], Appendix A.1" ([7] is Beuzart-Plessis, below),
    `σ(g) = 1 + log ‖g‖`, `Ξ^{[G]}` (2.9), Lemma 2.1, and
    (2.10) `∫_{[G]} (1 + σ_{[G]}(x))^{-d_G} Ξ^{[G]}(x)² dx < ∞`;
  - p.9: the Harish-Chandra Schwartz space `𝒞([G])`:
    `|(R_u φ)(x)| ≪ σ_{[G]}(x)^{-n} Ξ^{[G]}(x)` for all `n` and `u ∈ U(𝔤_∞)`;
  - pp.11–12: Lemma 3.2, Definition 3.3 (tempered automorphic forms, after Franke), and
    Bernstein's `[G]`-temperedness, "there exists `d > 0` such that for every of its derivatives
    by elements of `U(𝔤_∞)`, `φ` verifies `(1 + σ_{[G]})^{-d} φ ∈ L²([G])`", with
    Proposition 3.5 (for `φ ∈ 𝒜(G)`, tempered ⇔ `[G]`-tempered);
  - Lemma 3.10 (ii) (a tempered form all of whose weak constant terms lie in `𝒜^{temp,c}` is
    zero);
  - p.20: Proposition 5.4, for `a` smooth and compactly supported on `i𝔞_P^*` and `φ ∈ A^2_P(G)`,
    the wave packet `E_a = ∫_{i𝔞_P^*} a(λ) E_P(·, φ, λ) dλ` is in `𝒞([G])` (Remark 5.5: due to
    Franke);
  - pp.11–12, before Proposition 3.5: with Bernstein's standard measure
    `dm_X = (Ξ^{[G]})² dx`, (2.10) and Bernstein's Criterion give the summability of the weight
    `σ_{[G]}^d` (Delorme writes "the weight `σ_{[G]}^{-d}`", the density `w⁻¹` of the Criterion);
    the proof of Proposition 3.5 works with `w = σ_{[G]}^d` and the Key Lemma;
  - p.22: Theorem 6.1 (the isometry `ℰ̄` of Lapid's Theorem 2) and Lemma 6.2 (the wave packets of
    Proposition 5.4 lie in the image of `ℰ`);
  - Theorem 7.1 and pp.33–35: Proposition 7.8, Theorem 7.9 ("The image of the map `Ē` of
    Theorem 6.1 is equal to `L²(G(F) \ G(𝔸))`"), the preliminary remark after it ("From [5], end of
    section 3.5, automorphic forms which may contribute to the spectrum … are `[G]`-tempered.
    Hence they are tempered, by Proposition 3.5"), Lemma 7.10 and its proof ("similar to [10],
    Lemma 11", where [10] is J. Carmona and P. Delorme, *Transformation de Fourier sur l'espace
    de Schwartz d'un espace symétrique réductif*, Invent. Math. 134 (1998) 59–99), Lemma 7.11,
    and the end of the proof of Theorem 7.9.
- J. Bernstein, *On the support of Plancherel measure*, J. Geom. Phys. 5 (1988) 663–710,
  registered as `bernstein-1988-support-plancherel` (PDF page = printed page − 662): §3.1
  (p.681: an `S_w`-tempered form `β` satisfies `β(V^∞) ⊂ L²(X, w⁻¹ μ_X)`), §3.2 (p.682,
  the central Theorem: for a summable weight `w` the inclusion `S_w → L²(X)` is fine, hence
  Cond(w): only `S_w`-tempered forms contribute to the spectral decomposition of `L²(X)`),
  the Criterion p.685 (`w` is summable if and only if `∫_X w⁻¹ dm_X < ∞`) and the Key Lemma
  p.686.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*,
  Clay Math. Proc. 13 (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (PDF page = printed page + 9):
  §2 (p.311, the Eisenstein series `E(φ, λ)(x) = ∑ φ(γx) exp⟨λ, H_P(γx)⟩`, the normalization of
  the Library's `IsIwasawaCompact.parameterTwist` and `eisensteinSeries`) and Theorem 2 (p.314).
- J. Arthur, *An introduction to the trace formula*, in Clay Math. Proc. 4 (2005), registered as
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (PDF page = printed page + 12): p.34,
  the formal identities `E(x, I_P(λ, y)φ, λ) = E(xy, φ, λ)` and
  `M(s, λ) I_P(λ, y) = I_{P'}(sλ, y) M(s, λ)`, and the density of the space `H⁰_P` of
  `K`-finite, `𝒵`-finite vectors in `H_P`; p.35, Theorem 7.2 (Langlands): (a) `M(s, λ)` is
  unitary for `λ ∈ i𝔞_P^*`; (b) the wave packet map extends to a unitary map from `L̂_𝒫` onto a
  closed `G(𝔸)`-invariant subspace, intertwining `R̂_𝒫`, `(R̂_𝒫(y)F)_P(λ) = I_P(λ, y)F_P(λ)`,
  with right translation.
- R. Beuzart-Plessis, *Comparison of local spherical characters and the Ichino–Ikeda conjecture
  for unitary groups*, arXiv:1602.06538v2 (2017), Delorme's reference [7], registered as
  `beuzart-plessis-2017-comparison-local-spherical-characters-arxiv-v2`: Appendix A.1,
  pp.37–40 (PDF page = printed page). An abstract norm on a set `X` is a function
  `X → [1, ∞)`; for an affine variety `X` over `F` and generators `P_1, …, P_k` of `F[X]`,
  `‖x‖_{X_v} = max(1, |P_1(x)|_v, …, |P_k(x)|_v)` with the normalized absolute value `|·|_v`,
  and `‖x‖_X = ∏_v ‖x_v‖_{X_v}` on `X(𝔸)`. A norm on `X(𝔸)` is any abstract norm equivalent to
  `‖·‖_X` (each bounded by `C` times a power of the other); the class does not depend on the
  generators. For an affine group, `‖x‖_{[G]} = inf_{γ ∈ G(F)} ‖γ x‖_G` (p.40).
- Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series*, I.2.2 (heights) and I.2.17
  (automorphic forms), as used by the Library's `RepresentationGrowth.adelicSourceNorm` and
  `IsAutomorphicFunctionOn`.
- Library: `Langlands.GroupScheme.parabolicContainsMinimalStatement` (every rational parabolic
  contains a minimal one) and `Langlands.GroupScheme.minimalParabolicConjugacy` (minimal
  parabolics are conjugate by a rational point; Borel–Tits), used in the reduction of
  non-standard parabolics below.

## Definitions

### `rationalLogHeight F G rho : RationalQuotient F G → ℝ`

`σ_{[G]}(y) = 1 + log max(1, inf_{q ∈ G(F)} ‖q · y.out‖_ρ)`, where
`‖g‖_ρ = RepresentationGrowth.adelicSourceNorm F G rho g` is the Mœglin–Waldspurger height of
the matrix embedding `rho`: the normalized product over all places of the largest absolute value
of the entries of `rho(g)` and `rho(g)⁻¹`. It does not depend on the representative `y.out`,
since the infimum runs over all of `G(F)`.

Provenance. Delorme (p.8) fixes "a norm `‖.‖` on `G(𝔸)` as in [7], Appendix A.1", where [7] is
Beuzart-Plessis, puts `σ = 1 + log ‖·‖`, and by (2.6) for `P = G` sets
`σ_{[G]}(g) = inf_{γ ∈ G(F)} σ(γ g)`. The Lean function is this `σ_{[G]}` for the norm
`‖g‖ = max(1, ‖g‖_ρ)`:

- The formula. `max(1, ·)` and `log` are monotone and continuous, and the infimum runs over a
  nonempty set of nonnegative reals. So
  `inf_γ (1 + log max(1, ‖γ g‖_ρ)) = 1 + log max(1, inf_γ ‖γ g‖_ρ)`, the Lean expression.
- `max(1, ‖·‖_ρ)` is a norm in the sense of Beuzart-Plessis (Sources) when `rho` is a closed
  embedding, the hypothesis `IsClosedSubgroup rho` of every statement below. Let `N > 0`. The
  algebra `F[GL_N]` is generated by the entries of `g` and of `g⁻¹` (`1/det g = det(g⁻¹)`), and
  `F[GL_N] → F[G]` is surjective, so the pulled-back entries of `rho` and `rho⁻¹` generate
  `F[G]`. For these generators Beuzart-Plessis' norm is `‖g‖_G = ∏_v max(1, h_v(g))`, where
  `h_v(g)` is the largest normalized absolute value at `v` of the entries of `rho(g)` and
  `rho(g)⁻¹`, and `‖g‖_ρ = ∏_v h_v(g)`. In `Langlands/Global/AdelicRepresentationHeight.lean`,
  `h_v = finiteLocal ≥ 1` at the finite places (`one_le_finiteLocal`), and
  `h_v = infiniteLocal ^ (mult v)` with `N · infiniteLocal ≥ 1` (`one_le_nat_mul_localMaximum`)
  at the infinite places. So `max(1, h_v) = h_v` at the finite places and
  `h_v ≤ max(1, h_v) ≤ N^{mult v} h_v` at the infinite ones. As `∑_{v | ∞} mult v = [F : ℚ]`,
  `max(1, ‖g‖_ρ) ≤ ‖g‖_G ≤ N^{[F:ℚ]} ‖g‖_ρ ≤ N^{[F:ℚ]} max(1, ‖g‖_ρ)`. Thus `max(1, ‖·‖_ρ)`
  takes values in `[1, ∞)` and is equivalent to `‖·‖_G`.
- The truncation is needed: the raw `‖·‖_ρ` can be smaller than `1`, so it is not an abstract
  norm. For the identity embedding of `GL_2` over `ℚ`, the rotation with rows `(3/5, −4/5)` and
  `(4/5, 3/5)` at the real place and the identity at every finite place has `‖g‖_ρ = 4/5`.
- `N = 0`. A closed embedding into the trivial group `GL_0` forces `G` to be trivial. Then
  `F[G] = F` is generated by `1`, Beuzart-Plessis' norm for this generator is constantly `1`,
  and his `σ_{[G]}` is `1`. In the Library the height of the empty matrix is `0` (the maximum
  over an empty set of entries), and the Lean `σ_{[G]}` is `1 + log max(1, 0) = 1`. Without
  `IsClosedSubgroup rho`, `N = 0` would give `σ_{[G]} = 1` for every `G`, which is not
  Delorme's height; every statement below assumes `IsClosedSubgroup rho`.
- Other norms of the class. If `‖·‖'` is another Beuzart-Plessis norm, then
  `‖g‖' ≤ C ‖g‖^r` and `‖g‖ ≤ C ‖g‖'^r` for some `C, r ≥ 1`. As both norms are `≥ 1`,
  `1 + log ‖g‖' ≤ (r + log C)(1 + log ‖g‖)`, and the same holds after taking infima over `G(F)`.
  So the corresponding functions `σ_{[G]}` agree up to a bounded factor.

Every condition below has the form "`Θ σ_{[G]}^m ∈ L²` for all `m`" or
"`Φ σ_{[G]}^{-m} ∈ L²` for some `m`", and such conditions do not change when `σ_{[G]}` changes by
a bounded factor or when `1 + σ_{[G]}` replaces `σ_{[G]}`.

### `IsWavePacket F G K rho hsmooth hcalc Θ`

`Θ` is one of the functions quantified in the hypothesis of
`WavePacketCompletenessStatement`. The data are a parabolic `p : P → G` with geometric unipotent
radical `iU`, Levi `l` and presentation `r` (all instance hypotheses of the target, here
existentially quantified), `hK : IsIwasawaCompact p K`, coordinates
`e : ℝ^n ≃ X^*(P) ⊗ ℝ`, forms `v j ∈ A^2_P` (`IsSquareIntegrableInducedForm`), smooth compactly
supported `c j`, and functions `E j`. Each `E j` is meromorphic with domain of holomorphy
`D ⊇ i𝔞_P^*` and agrees with `hK.eisensteinSeries (v j)` for `Re λ` sufficiently regular. The
condition is
`Θ = fun g => ∫ x, ∑ j, c j x * E j (imaginaryParameter F P (e x)) g ∂(spectralMeasure n)`.
The conditions are word for word those of the target, in the same order.

For parabolics containing `P₀` these are Delorme's wave packets `E_a` of Proposition 5.4:
`a(λ) φ` corresponds to `∑ j, c j x • v j` at `λ = i e(x)`. The normalization of
`spectralMeasure` only multiplies `Θ` by a constant. The packets of the other parabolics are
treated in "Non-standard parabolics" below.

### `IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ`

`Φ : G(𝔸) → ℂ` satisfies three conditions:

1. `IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) (K.comap (ofInfinite F G))
   rho Φ`. This means `Φ` is an automorphic form on `G(F) \ G(𝔸)` in the sense of
   Mœglin–Waldspurger I.2.17: left `G(F)`-invariant, smooth, finite under the archimedean part of
   `K`, `𝔷`-finite and of moderate growth. It is the same notion that `IsSquareIntegrableInducedForm`
   uses for `U(𝔸) M(F) \ G(𝔸)`.
2. There is `ν ∈ X^*(G) ⊗ ℝ` with `Φ(a g) = a^{iν} Φ(g)` for all
   `a ∈ RestrictionSplitCentre.canonicalSubgroup F G` (the split component `A_G`) and
   `g ∈ G(𝔸)`, where `a^{iν} = parameterPower F G (imaginaryParameter F G ν) a`. This is Delorme's
   "transforming under a unitary character `ν_G` of `𝔞_G`" (Lemma 7.10). Every unitary character
   of `A_G ≅ 𝔞_G` has this form, because `H_G` identifies `A_G` with `𝔞_G`.
3. There is `m : ℕ` with `y ↦ Φ(y.out) / σ_{[G]}(y)^m` in `L²([G], μG)`, for the measure `μG`
   of the target. This is Bernstein's `[G]`-temperedness of `Φ` itself.

Provenance (derived): Delorme's Lemma 7.10 produces a tempered automorphic form (Definition 3.3)
with a unitary `𝔞_G`-character. By Proposition 3.5 a tempered form is `[G]`-tempered, which
includes condition 3. Conversely, condition 3 controls only `Φ`, and Delorme's
`[G]`-temperedness also asks it of the derivatives `R_u Φ`, `u ∈ U(𝔤_∞)`. For automorphic forms
the two coincide. Harish-Chandra's theorem gives `α ∈ C_c^∞(G_∞)` with `Φ = Φ * α`: `Φ` is
`K_∞`-finite and annihilated by an ideal of finite codimension in `𝔷`, uniformly in the
finite-adelic variable. Then `R_u Φ = Φ * R_u α`. Since `σ_{[G]}(x y) ≤ σ_{[G]}(x) + C` for `y`
in the support of `R_u α`, the bound `‖Φ σ_{[G]}^{-m}‖₂ < ∞` passes to `R_u Φ`. So by
Proposition 3.5 the definition is equivalent to "tempered, with a unitary `A_G`-character".
Delorme's `(1 + σ_{[G]})^{-d}` with real `d > 0` is replaced by `σ_{[G]}^{-m}` with natural `m`,
which is equivalent because `1 ≤ σ_{[G]}`.

## Statements

All four statements carry the hypotheses of `WavePacketCompletenessStatement` unchanged. These
are: `F : Type` a number field; `G` affine, locally of finite type and connected reductive; `K`
maximal compact; `rho` closed; `hsmooth`, `hcalc`; a minimal parabolic `P₀` with
`IsIwasawaCompact p₀ K`; and the measure
`μG = LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G) _ Measure.haar` on
`[G] = RationalQuotient F G`. "Orthogonal" means the target's pairing
`∫ y, f y * conj (Θ y.out) ∂μG = 0`. Right translation `R(g)`, `(R(g) f)(y) = f(y g)`, is
`LeftCosetSpace.rightTranslate`; it is unitary on `L²([G], μG)` because `μG` is right
`G(𝔸)`-invariant.

### `SpectralWitnessStatement` (Delorme, Lemma 7.10; Bernstein 1988)

The statement concerns a set `W` of functions on `G(𝔸)` with two properties:

- (rapid decay) for every `Θ ∈ W` and every `m : ℕ`,
  `y ↦ Θ(y.out) · σ_{[G]}(y)^m` is in `L²([G])`;
- (invariance) for every `f ∈ L²([G])` orthogonal to `W` and every `g ∈ G(𝔸)`, the right
  translate `y ↦ f(y g)` (`LeftCosetSpace.rightTranslate`) is orthogonal to `W`.

For such `W`, every `f ∈ L²([G])` orthogonal to `W` with `¬ f =ᵐ[μG] 0` yields a function `Φ`
with `IsLogSquareIntegrableAutomorphicForm Φ`, `Φ g ≠ 0` for some `g`, and
`∫ y, Φ(y.out) · conj Θ(y.out) ∂μG = 0` for every `Θ ∈ W`.

Correspondence: this is Lemma 7.10 with the image of `Ē` replaced by the abstract family `W`. Its
proof, which Delorme models on Carmona–Delorme 1998, Lemma 11 (his reference [10]), uses
exactly the two listed properties of the wave packets. Delorme takes `H = (image of Ē)^⊥`, a
nonzero closed `G(𝔸)`-invariant subspace. Here `H = W^⊥` is closed; it is stable under every
right translation `R(g)` by the invariance hypothesis, so it is a unitary representation of
`G(𝔸)` (`μG` is right invariant); and it is nonzero because it contains `f`. He decomposes `H`
as a direct integral `∫ H_π dμ(π)` and disintegrates evaluation at `1` on `H^∞` into
`G(F)`-invariant distribution vectors `ξ_π`. He takes a `K`-finite smooth `v ≠ 0` in `H` and the
matrix coefficients `⟨ξ_π, π(g) v_π⟩`, and uses the preliminary remark.

The weights in the preliminary remark are as follows. Bernstein's Criterion (p.685) says that a
weight `w` is summable if and only if `∫ w⁻¹ dm_X < ∞`, and Delorme (pp.11–12) takes the standard
measure `dm_X = (Ξ^{[G]})² dx`. By (2.10), `w = (1 + σ_{[G]})^d` is therefore summable for
`d ≥ d_G`. For this `w`, Bernstein's Theorem of §3.2 gives Cond(w), and by §3.1 the forms that
contribute to the spectral decomposition of `H` lie, with all their `U(𝔤_∞)`-derivatives, in
`L²([G], w⁻¹ dx) = L²([G], (1 + σ_{[G]})^{-d} dx)`: the density is `w⁻¹`, not `w`. In the Lean
condition `Φ / σ_{[G]}^m ∈ L²([G])` the squared norm is `∫ |Φ|² σ_{[G]}^{-2m} dμG`, so the weight
is `σ_{[G]}^{-2m}`. Since `σ_{[G]} ≤ 1 + σ_{[G]} ≤ 2 σ_{[G]}`, the contributing forms satisfy
the Lean condition for every natural `m ≥ d / 2`.

Almost every such coefficient is then a `[G]`-tempered automorphic form (`𝔷`-finite and with an
`A_G`-character since `π` is irreducible), bounded by `p Ξ (1 + σ_{[G]})^q`. Fubini then needs
`∫ |E_a| Ξ (1 + σ_{[G]})^q < ∞`. Delorme obtains it from `E_a ∈ 𝒞([G])`. For an abstract `W`
the tests need not be measurable functions: `MemLp` gives only that `y ↦ Θ(y.out)` is almost
everywhere equal to a strongly measurable function (see "Integrals" below). So first replace
each `Θ ∈ W` by a strongly measurable `Θ̃` on `[G]` with `Θ̃ = Θ(·.out)` `μG`-almost everywhere
(`AEStronglyMeasurable.mk`). This preserves the weighted `L²` conditions (`MemLp.ae_eq`) and
every Bochner pairing, with `f`, its right translates and `Φ` (`integral_congr_ae`). The
invariance hypothesis and the conclusion only involve these pairings, so the argument may be run
for the family of the `Θ̃`. For `Θ̃` the integrability follows from the rapid-decay hypothesis
and Cauchy–Schwarz:
`∫ |Θ̃| Ξ (1 + σ)^q ≤ ‖Θ̃ (1 + σ)^{q + d_G/2}‖₂ ‖Ξ (1 + σ)^{-d_G/2}‖₂`, where the second factor
is finite by (2.10) and the first is bounded by `2^{m} ‖Θ̃ σ^{m}‖₂` for a natural
`m ≥ q + d_G/2`, and Fubini applies to `Θ̃`. The separability argument for `π₀` uses that the
classes of the `Θ̃` lie in the separable Fréchet space `⋂_m σ_{[G]}^{-m} L²([G])`. Delorme's
orthogonality `∫ E_a Φ̄ = 0` is the complex conjugate of the pairing used here.

### `WavePacketRapidDecayStatement` (Delorme, Proposition 5.4)

For every `Θ` with `IsWavePacket Θ` and every `m : ℕ`, `y ↦ Θ(y.out) · σ_{[G]}(y)^m` is in
`L²([G])`.

Correspondence: Proposition 5.4 gives `E_a ∈ 𝒞([G])`, so `|E_a| ≪_n σ_{[G]}^{-n} Ξ^{[G]}`
for all `n`. Taking `2n ≥ 2m + d_G`, (2.10) gives `E_a σ_{[G]}^m ∈ L²`. The `E j` of
`IsWavePacket` are the meromorphic continuations of the Eisenstein series. A meromorphic `E j`
with dense open domain of holomorphy `D` (`IsMeromorphicInCoordinatesOn`, local quotients `h/g`
on connected neighbourhoods) equal to `E(v j, λ)` on an open set is uniquely determined, so `Θ`
is Delorme's `E_a`. `Θ` is left `G(F)`-invariant, so `Θ(y.out)` does not depend on the
representative.

Scope bridge: Proposition 5.4 is stated for parabolics containing `P₀` and `K` in good position.
Packets of other parabolics are reduced to these by rational conjugation, step 4 of
"Non-standard parabolics" below; the passage from `K` to a compact subgroup in good position is
that of the target's Markdown ("The compact subgroup").

### `WavePacketOrthogonalTranslationStatement` (Delorme Theorem 6.1 and Lemma 6.2; Arthur Theorem 7.2)

For `f ∈ L²([G])` orthogonal to every `Θ` with `IsWavePacket Θ`, every `g ∈ G(𝔸)` and every
such `Θ`, the translate `y ↦ f(y g)` is orthogonal to `Θ`.

Correspondence: Delorme decomposes `H = (image of ℰ̄)^⊥` as a representation of `G(𝔸)` in the
proof of Lemma 7.10, so he uses that the image of `ℰ̄` is `G(𝔸)`-invariant without stating it.
This is the intertwining part of Langlands' theorem as stated in Arthur's Theorem 7.2 (b), which
does not involve the decomposition (7.5). For the packets of `IsWavePacket` the derivation is
the following (explanatory, not proved here). Write `R(h)` for right translation by `h` and
`H_P` for the Hilbert completion of `A^2_P`; first let `P` contain `P₀`.

1. A translate is not a packet of the same form. With the Library's normalization
   `E(v, λ)(x) = ∑_{δ ∈ P(F) \ G(F)} v(δx) exp⟨λ, H_P(δx)⟩` (Lapid §2), the series give
   `R(h) E(v, λ) = E(I_P(λ, h) v, λ)` with
   `(I_P(λ, h) v)(x) = v(xh) exp⟨λ, H_P(xh) − H_P(x)⟩` (Arthur p.34). The exponential factor
   depends on `λ`. (The identity holds where the series converge; on `i𝔞_P^*` it enters only
   through step 3.) So `R(h) Θ` is the packet of the section `λ ↦ ∑ j, c j · I_P(λ, h)(v j)`,
   which in general is neither of the form `∑ j, c j ⊗ v j` nor `K_∞`-finite. Even for
   `P = G = 𝔾_m` over `ℚ` the factor cannot be dropped: there `R(h)` multiplies `E(1, λ)` by
   `exp⟨λ, H_G(h)⟩`, which varies with `λ`.
2. The closed span for one parabolic. Let `S_P` be the closed span in `L²([G])` of the packets of
   `IsWavePacket` for `P`. For `ψ = ∑ j, c j ⊗ v j`, an element of Delorme's `𝒲_P`, the
   argument of Lemma 6.2 gives `Θ_{P,ψ} = ℰ(F^ψ)` with
   `F^ψ_Q(λ) = ∑_{s ∈ W(P|Q)} M(s, s⁻¹λ) ψ(s⁻¹λ)`. As `M(s, λ)` is unitary on `i𝔞_P^*`
   (Arthur, Theorem 7.2 (a)), `‖F^ψ‖ ≤ C ‖ψ‖` with `‖ψ‖` the norm of `L²(i𝔞_P^*; H_P)`. As
   `ℰ̄` is an isometry (Theorem 6.1), `ψ ↦ Θ_{P,ψ}` extends to a bounded linear map `T_P` on
   `L²(i𝔞_P^*; H_P)`. The sections `∑ j, c j ⊗ v j` are dense in that space, because `A^2_P`,
   Arthur's `H⁰_P`, is dense in `H_P` (Arthur p.34). Hence `S_P` is the closure of the image of
   `T_P`.
3. Equivariance. Let `G(𝔸)` act unitarily on `L²(i𝔞_P^*; H_P)` by
   `(I(h)ψ)(λ) = I_P(λ, h) ψ(λ)`. The symmetrization `ψ ↦ F^ψ` intertwines `I` with Arthur's
   `R̂_𝒫`, since `M(s, λ) I_P(λ, h) = I_{P'}(sλ, h) M(s, λ)` (Arthur p.34). And `ℰ̄` intertwines
   `R̂_𝒫` with `R` (Arthur, Theorem 7.2 (b)). So `T_P(I(h)ψ) = R(h) T_P(ψ)`. In particular
   `R(h) Θ_{P,ψ}` is the `L²` limit of the packets `T_P(ψ_n)` for any sections
   `ψ_n = ∑ j, c_{n,j} ⊗ v_{n,j}` converging to `I(h)ψ`. No finite-dimensional or
   regular-support hypothesis on the `ψ_n` is needed, since only the `L²` continuity of `T_P` is
   used. Therefore `R(h) S_P ⊆ S_P` for every `h`, and `R(h) S_P = S_P`.
4. Conclusion. For parabolics not containing `P₀`, step 4 of "Non-standard parabolics" below
   gives `R(h) S_P = S_P` too. The closed span `S` of all packets of `IsWavePacket` is the
   closed span of the `S_P`, so `R(h) S = S`. As `μG` is right invariant, `R(h)` is unitary and
   `S^⊥` is stable under every `R(h)`. If `f` is orthogonal to every packet, then `f ∈ S^⊥`, so
   `R(g) f ∈ S^⊥`, which is the Lean conclusion `∫ f(y g) · conj Θ(y) dμG = 0`.

### `TemperedWavePacketVanishingStatement` (Delorme §7)

If `IsLogSquareIntegrableAutomorphicForm Φ` and `∫ y, Φ(y.out) · conj Θ(y.out) ∂μG = 0` for
every `Θ` with `IsWavePacket Θ`, then `Φ g = 0` for all `g ∈ G(𝔸)`.

Correspondence: this is the part of the proof of Theorem 7.9 after Lemma 7.10. By Proposition 3.5
(see the provenance of `IsLogSquareIntegrableAutomorphicForm`), `Φ` is tempered with a unitary
character `ν_G`. For `a = a₁ ⊗ a₂` the pairing factors as `a₂(ν_G) ∫_{[G]^1} E_{a₁} Φ̄`, and such
`a` occur as `c ∘ e⁻¹` among the wave packets of `IsWavePacket`. Lemma 7.11, proved with
Theorem 7.1 and Proposition 7.8, expresses `∫_{[G]^1} E_{a₁} Φ̄` through the weak constant terms
`Φ_{P,0,μ}`. Its vanishing for all `P`, `φ`, `a₁`, `a₂` gives `Φ_{P,0,μ} ∈ 𝒜^{temp,c}_P(G)`,
and Lemma 3.10 (ii) gives `Φ = 0`. `Φ` is continuous, so `Φ = 0` as an automorphic form means
`Φ g = 0` for every `g`. Only the packets of parabolics containing `P₀` are used, as in Delorme;
the orthogonality to the other packets is an unused part of the hypothesis. The passage from `K`
to a compact subgroup in good position is that of the target's Markdown ("The compact
subgroup").

### Non-standard parabolics

`IsWavePacket` ranges, as the target's hypothesis does, over every presented parabolic `P` with
`P(𝔸)K = G(𝔸)`. The sources treat the parabolics containing a fixed minimal parabolic `P₀`.
For `SpectralWitnessStatement` (an abstract family `W`) and
`TemperedWavePacketVanishingStatement` (where the larger family only strengthens the hypothesis)
this changes nothing. `WavePacketRapidDecayStatement` and
`WavePacketOrthogonalTranslationStatement` must cover all these packets. Their proofs reduce to
parabolics containing `P₀` by rational conjugation, as follows (explanatory, not proved here;
`P₀` is the minimal parabolic of the hypothesis, with `P₀(𝔸)K = G(𝔸)`).

1. Conjugation to a standard parabolic. `P` contains a minimal parabolic `P₁`
   (`parabolicContainsMinimalStatement`), and `P₁ = γ⁻¹ P₀ γ` for some `γ ∈ G(F)`
   (`minimalParabolicConjugacy`). Then `P' = γ P γ⁻¹` contains `P₀`. Its Levi, unipotent
   radical, split component and presentation are the images of those of `P` under the inner
   automorphism `Int(γ)` (`G.innerIso`).
2. The conjugate compact subgroup. `K` acts transitively on `G(𝔸)/P₀(𝔸)`, and
   `x P₁(𝔸) ↦ x γ⁻¹ P₀(𝔸)` is a `K`-equivariant bijection `G(𝔸)/P₁(𝔸) → G(𝔸)/P₀(𝔸)`. So
   `P₁(𝔸)K = G(𝔸)`. Hence `K' = γ K γ⁻¹` is a maximal compact subgroup with
   `P₀(𝔸)K' = γ P₁(𝔸) K γ⁻¹ = G(𝔸)`. So `K'` satisfies the hypotheses of the statements, with the
   same `P₀`, and `P'(𝔸)K' = G(𝔸)`.
3. Transport of the inducing data and of the packet. Put `v'(x) = v(γ⁻¹ x γ)`.
   - `v'` is left invariant under `M'(F) U'(𝔸) = γ M(F) U(𝔸) γ⁻¹`, because `γ` is rational. It
     is smooth, `K'_∞`-finite, `𝔷`-finite (`𝔷` is invariant under `Ad`), of moderate growth (the
     norm `max(1, ‖·‖_ρ)` of `γ⁻¹ x γ` is at most a constant times that of `x`, by the
     submultiplicativity below), and
     `A_{P'}`-equivariant.
   - The integrability condition of `IsSquareIntegrableInducedForm` for `K'` is the one for `K`.
     Under `(k, m) ↦ (γ k γ⁻¹, γ m γ⁻¹)` the integrand for `v'` becomes the integrand for `v`,
     and the modulus characters correspond. Conjugation by the rational `γ` carries the Haar
     probability of `K` to that of `K'`. It also carries the measure on the quotient of `M(𝔸)`
     to the corresponding measure for `M'` up to a positive constant (product formula), which
     does not affect integrability.
   - If `x = q k` with `q ∈ P(𝔸)` and `k ∈ K`, then `γ x γ⁻¹ = (γ q γ⁻¹)(γ k γ⁻¹)`. So
     `H^{K'}_{P'}(γ x γ⁻¹) = Ad(γ) H^K_P(x)`.
   - `δ ↦ γ δ γ⁻¹` maps `P(F) \ G(F)` onto `P'(F) \ G(F)`. So
     `E^{K'}_{P'}(v', Ad(γ)λ)(γ x γ⁻¹) = E^K_P(v, λ)(x)` where the series converge, and the
     meromorphic continuations `E j` correspond.
   - With the coordinates `e' = Ad(γ) ∘ e` and the same `c j` and `spectralMeasure n`, the
     transported data define a packet `Θ'` of `IsWavePacket` for `(P', K')` with
     `Θ'(γ x γ⁻¹) = Θ(x)`. As `Θ'` is left `G(F)`-invariant, `Θ'(γ x γ⁻¹) = Θ'(x γ⁻¹)`. So
     `Θ = R(γ⁻¹) Θ'`, and the same correspondence identifies the packets of `(P, K)` with the
     `R(γ⁻¹)`-translates of the packets of `(P', K')`.
4. Transport of the conclusions.
   - Rapid decay. For `N > 0` the Library's `adelicHeight = N^{[F:ℚ]} ‖·‖_ρ` is at least `1`
     and submultiplicative (`one_le_adelicHeight`, `adelicHeight_mul_le`), so the norm
     `‖g‖ = max(1, ‖g‖_ρ)` satisfies `‖x y‖ ≤ N^{[F:ℚ]} ‖x‖ ‖y‖` (for `N = 0`, `σ_{[G]} = 1`).
     So `|σ_{[G]}(y γ) − σ_{[G]}(y)| ≤ c_γ`, and `μG` is right invariant. Hence
     `Θ σ_{[G]}^m ∈ L²` for all `m` if and only if `Θ' σ_{[G]}^m ∈ L²` for all `m`. The case of
     parabolics containing `P₀`, applied to `K'`, gives the result for `Θ`.
   - Translation. `R(γ⁻¹)` maps the closed span `S_{P',K'}` of the packets of `(P', K')` onto
     `S_{P,K}`. Steps 1–3 of the translation correspondence, applied to `K'`, give
     `R(h) S_{P',K'} = S_{P',K'}` for every `h`. So
     `R(h) S_{P,K} = R(γ⁻¹) R(γ h γ⁻¹) S_{P',K'} = S_{P,K}`.

### Integrals

All integrals are Bochner integrals, which are `0` for non-integrable integrands. In the
pairings of `SpectralWitnessStatement` and `TemperedWavePacketVanishingStatement`, the integrand
`Φ(y.out) · conj Θ(y.out)` is integrable by Cauchy–Schwarz: `Φ σ_{[G]}^{-m}` and `Θ σ_{[G]}^m`
are in `L²`, the latter by the rapid-decay hypothesis or by `WavePacketRapidDecayStatement`. The
pairings with `f ∈ L²` are integrable since `Θ ∈ L²`. So no hypothesis holds only through the
value `0` of a divergent integral.

Measurability. `MemLp` includes only almost-everywhere strong measurability
(`MemLp.aestronglyMeasurable`). With `m = 0`, the rapid-decay condition makes `y ↦ Θ(y.out)`
almost everywhere equal to a strongly measurable function, but not necessarily measurable
itself: a test may be changed on a non-measurable subset of a `μG`-null set. In
`SpectralWitnessStatement` the hypotheses and the conclusion depend on a test `Θ ∈ W` only
through the `μG`-almost-everywhere class of `y ↦ Θ(y.out)` (`MemLp.ae_eq`,
`integral_congr_ae`), so its proof may work with strongly measurable representatives, as in
its Fubini step above.

## The reduction theorem

`wavePacketCompleteness_of_reduction` takes `SpectralWitnessStatement`,
`WavePacketRapidDecayStatement`, `WavePacketOrthogonalTranslationStatement` and
`TemperedWavePacketVanishingStatement` and proves `WavePacketCompletenessStatement`.

Proof (as implemented): introduce the data of the target and `f ∈ L²([G])` orthogonal to all of
its wave packets.

1. Destructuring `IsWavePacket Θ` gives exactly the arguments of the target's orthogonality
   hypothesis. So `f` is orthogonal to every `Θ` with `IsWavePacket Θ`.
2. Suppose `¬ f =ᵐ[μG] 0`. Apply `SpectralWitnessStatement` to `W = {Θ | IsWavePacket Θ}`. The
   rapid-decay hypothesis is `WavePacketRapidDecayStatement` and the invariance hypothesis is
   `WavePacketOrthogonalTranslationStatement`. This gives `Φ` with
   `IsLogSquareIntegrableAutomorphicForm Φ`, `Φ g ≠ 0` for some `g`, and `Φ` orthogonal to `W`.
3. `TemperedWavePacketVanishingStatement` gives `Φ g = 0`, a contradiction.

This mirrors the structure of Delorme's proof of Theorem 7.9 (contradiction through Lemma 7.10).
The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Scope

None of the four statements is proved here. Separate `lean.proof@1` tasks for them follow
once this module is accepted. Their expected inputs:

- `SpectralWitnessStatement`: direct integral decomposition of unitary representations of
  `G(𝔸)`, Bernstein 1988 §3, Delorme Proposition 3.5 and (2.10), and Harish-Chandra's results
  on `𝔷`-finite vectors of irreducible unitary representations;
- `WavePacketRapidDecayStatement`: Delorme §4–§5 (uniform temperedness of Eisenstein series,
  Lapid's Lemma 4, Proposition 5.4), and the conjugation of "Non-standard parabolics";
- `WavePacketOrthogonalTranslationStatement`: Delorme's Theorem 6.1 (the published isometry
  statements of the Library) and the argument of Lemma 6.2, the unitarity of `M(s, λ)` on
  `i𝔞_P^*` and the intertwining identities of Arthur pp.34–35, and the conjugation of
  "Non-standard parabolics";
- `TemperedWavePacketVanishingStatement`: Delorme §3 (weak constant terms) and §7 (truncated
  inner products with Eisenstein series), with the published constant-term and continuation
  statements of the Library.

The transfer from `K` to a compact subgroup in good position, which the sources assume, is the
one described in the target's Markdown ("The compact subgroup") and belongs to these proofs.
