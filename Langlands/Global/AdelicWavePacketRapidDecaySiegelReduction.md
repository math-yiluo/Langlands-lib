# Rapid decay of wave packets from Siegel-set estimates

Module `Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction`, namespace
`Langlands.Global`.

The module states two propositions, `WavePacketSiegelDecayStatement` and
`SiegelDominatedIntegrabilityStatement`, and proves

```
theorem wavePacketRapidDecay_of_siegel (hdecay : WavePacketSiegelDecayStatement)
    (hint : SiegelDominatedIntegrabilityStatement) : WavePacketRapidDecayStatement
```

Neither proposition is proved here. The theorem is a reduction: it is not an unconditional
proof of `WavePacketRapidDecayStatement`. That statement, `IsWavePacket`,
`rationalLogHeight` and the other notions of the target are unchanged
(`Langlands/Global/AdelicWavePacketCompletenessReduction.lean`).

## Sources

- P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107,
  registered as `delorme-2023-spectral-theorem-langlands` (published PDF numbering). §2:
  Siegel domains (2.3), the inclusion (2.4), the norm and `σ` (2.6)–(2.8), (2.5), Lemma 2.1,
  (2.10) and the Schwartz space `𝒞([G])` (pp.7–9). §4.2: Proposition 4.1 (p.17). §5:
  Lemmas 5.1–5.3, Proposition 5.4 and its proof with the estimate (5.2) (pp.18–21).
- E. Lapid, *On the Harish-Chandra Schwartz space of G(F)\G(A)* (Delorme's reference [18]),
  registered as `lapid-2013-harish-chandra-schwartz-space-automorphic` (ESI preprint 2403,
  2012). §1–2: the Siegel domain `𝔰 = {g : H(g) ∈ T₁ + 𝔞₀⁺}`, (1) and `G(F) 𝔰 = G(𝔸)`
  (PDF p.5); the unfolding inequality (2), the inclusion (3) and `Ξ(pk) = δ_{P₀}(p)^{1/2}` on `𝔰`
  (PDF p.6); Lemma 2.1 (PDF pp.7–8); the quotient function
  `σ_L(g) = 1 + min_{x ∈ 𝔰 ∩ G(F) g} ‖H(x)‖`, its property 2 and property 5, equation (5):
  `Ξ σ_L^{-n} ∈ L²(P₀(F) \ 𝔰)` for `n > r/2` (PDF p.8). Delorme quotes (5) as "[18] section 2
  (9)" in his (2.5); in the registered preprint it is numbered (5). Lapid's `σ` is written
  `σ_L` below, as in Delorme.

## Definitions

Fix a number field `F : Type`, an affine group scheme `G` over `F` and a matrix representation
`rho : MatrixRepresentation G (Fin N)`.

- `adelicLogHeight F G rho x = 1 + log max(1, ‖x‖_ρ)`, with
  `‖x‖_ρ = RepresentationGrowth.adelicSourceNorm F G rho x`. This is Delorme's
  `σ(g) = 1 + log ‖g‖` (after (2.7)) for the norm `max(1, ‖·‖_ρ)` used by
  `rationalLogHeight`. The Library's `rationalLogHeight F G rho y` is the same expression
  with `‖x‖_ρ` replaced by its infimum over the coset `y = G(F) x`.
- For `T, i, ν, T₀, j` (the data of `IsSiegelAlgebraicSetup`, module
  `Langlands.Global.AdelicSiegelReductionStatement`) and `a` in the positive torus
  `A_{T₀} = PositiveRealTorus.intrinsicSubgroup F T₀`,

  `siegelModulus F G T i ν T₀ j a = ∏ᶠ_{β ∈ Φ⁺} |β(a)|^{m_β}`,

  where `Φ⁺ = positiveRelativeRoots i ν`, `|β(a)| = PositiveRealTorus.normCharacter F T₀ (j ≫ β) a`
  and `m_β = finrank F (weightSpace i β)`. It is the right side of the published
  `PositiveTorusUnipotentModulusStatement`, which the Library proves
  (`positiveTorusUnipotentModulus_of_coordinates` with `positiveTorusTriangularCoordinates`).
  So it equals the modulus `δ_{P₀}(a)` of conjugation by `a` on `N₀(𝔸)`, that is
  `e^{2ρ₀(H₀(a))}`.
- Relation to the two `Ξ` functions. Let `y = p e^X k` be a point of Lapid's domain `𝔰`
  (`p ∈ P₀(𝔸)¹`, `X ∈ T₁ + 𝔞₀⁺`, `k ∈ K`) for the standard data. Lapid's `𝔞₀` is the Lie
  algebra of a maximal split torus of all of `G`, so `𝔞₀ = 𝔞_G ⊕ 𝔞₀^G`. In the setup the torus
  `T₀` is a maximal split torus of the derived group and the split component supplies the
  central part, so `e^X = z a` with `z = e^{X_G} ∈ A_G` and `a ∈ A_{T₀}`; `a` is the standard
  torus coordinate of `y`. The simple roots vanish on `𝔞_G`, so `|β(a)| = |β(e^X)|`. Since
  `δ_{P₀}` is trivial on `P₀(𝔸)¹` and on the central `A_G`,
  `siegelModulus(a)^{1/2} = δ_{P₀}(p e^X)^{1/2}`. This *equals* Lapid's `Ξ(y)`. Delorme's quotient function `Ξ^{[G]}(x) = vol_{[G]}(xB)^{-1/2}` of (2.9)
  depends on the choice of the neighbourhood `B`. Only its equivalence class is canonical, and
  Lemma 2.1 (i) gives `Ξ^{[G]} ∼ e^{ρ(H₀)} ∼ Ξ` on a Siegel domain `𝔰_G`. So
  `siegelModulus^{1/2}` is only *comparable* to `Ξ^{[G]}` there, up to constants depending on
  `B` and the domain. `Ξ^{[G]}` is not used in this module.
- `IsSiegelPoint F G T i ν T₀ j C t Ω a x` says that

  `x = z · (n m a k) · w`, with `z ∈ A_G`, `n ∈ Ω_N`, `m ∈ Ω_M`, `|β(a)| ≥ t` for every simple
  relative root `β`, `k` in the compact subgroup of `C`, `w ∈ Ω`.

  Here `A_G = RestrictionSplitCentre.canonicalSubgroup F G` is the group `A_G^∞` of the
  target's `IsLogSquareIntegrableAutomorphicForm`. `C : CompactFactors …` supplies compact sets
  `Ω_N ⊆ N₀(𝔸)` and `Ω_M ⊆ M₀(𝔸)¹` and a compact subgroup. The chamber is
  `PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t`. The factors `n` and `m` are mapped
  into `G(𝔸)` by the standard unipotent and Levi inclusions, and `a` by
  `AdelicSiegelFactors.positiveMap`. The middle factor `n m a k` is exactly a point of the
  published `weakSiegelProduct` with its torus coordinate (`mem_productSet_iff`). We call the
  set of such `x` the Siegel set `A_G · Ω_N Ω_M A_{T₀}(t) K_C · Ω`, where `K_C` is the compact
  subgroup of `C`.

  This factor product is *analogous* to Delorme's Siegel domain (2.3) and to Lapid's `𝔰`. It
  is not the same notion, because its data are arbitrary. Delorme's (2.3) requires
  `G(𝔸) = G(F) 𝔰_G` (case `P = G`), and Lapid's `𝔰` satisfies `G(F) 𝔰 = G(𝔸)`.
  `IsSiegelPoint` imposes no such condition. For example, take `SL₂` over `ℚ` with identity
  prefix factors, trivial compact subgroup and `Ω = {1}`. Every point of that Siegel set has
  trivial finite component. So the finite components of its `G(F)`-saturation lie in the
  countable image of `G(F)`, and the saturation is not `G(𝔸)`. The two statements use the notion differently.
  `WavePacketSiegelDecayStatement` quantifies over *all* data. For
  `SiegelDominatedIntegrabilityStatement` some data must *exist*, and the derivation below
  chooses data whose Siegel set contains a representative of every `P₀(F)`-orbit in Lapid's
  `𝔰`.

## The two statements

Both statements keep the number-field universe `Type` and the instance hypotheses of the
target.

### `WavePacketSiegelDecayStatement`

The hypotheses are exactly those of `WavePacketRapidDecayStatement`. Let `G` be connected
reductive, `K` maximal compact, `rho` closed, `hsmooth` and `hcalc` given, and `p₀` a
minimal parabolic with `IsIwasawaCompact p₀ K`. Then every `Θ` with
`IsWavePacket F G K rho hsmooth hcalc Θ` satisfies:

1. `Θ` is continuous;
2. `Θ(q g) = Θ(g)` for `q ∈ G(F)` (`rationalSubgroup F G`);
3. for every algebraic Siegel setup `(T, i, ν, T₀, j)`, every `C` (with any compact subgroup),
   every threshold `t`, every compact `Ω ⊆ G(𝔸)` and every `n : ℕ` there is `B` with

   `‖Θ x‖ ≤ B · siegelModulus(a)^{1/2} / adelicLogHeight(x)^n`

   for every Siegel point `x` with torus coordinate `a`.

*Provenance (derived from Delorme's proof of Proposition 5.4).* Proposition 5.4 says
`Θ ∈ 𝒞([G])`. Its proof establishes (5.2) by induction on `dim 𝔞_0^G`:

`|Θ(exp X_G exp(sX) ω)| ≪_k (1 + ‖X_G‖)^{-k} (1 + s)^{-k} e^{sρ(X)}`

for `X_G ∈ 𝔞_G`, `X` in a neighbourhood `S₀` of a point of the unit sphere of the positive
chamber, `s > 0` and `ω` in an arbitrary compact `Ω`. It uses Proposition 4.1 (uniform
temperedness of Eisenstein series on compact sets of unitary parameters), Lemma 5.3 and
the weak constant term (4.3). Finitely many `S₀` cover the sphere, so

`|Θ(exp(Y) ω)| ≪_k (1 + ‖Y‖)^{-k} e^{ρ(Y)}` for `Y ∈ 𝔞_G ⊕ 𝔞_0^{G,+}`, `ω ∈ Ω`.

Item 3 follows. Write a Siegel point as `x = z a (a⁻¹ n a) m k w`:

- `m` commutes with `a`, because `M₀` centralizes `T`;
- `a⁻¹ Ω_N a` stays in a compact set for `|β(a)| ≥ t` (Delorme (2.4));
- `a` is a point `a⁺` of the closed positive chamber times an element of a compact box,
  because the simple roots give coordinates on `A_{T₀}`;
- `δ_{P₀}(a) ≍ e^{2ρ(H(a⁺))}`, and `A_G` is central with `ρ = 0` on `𝔞_G`.

The upper bound `adelicLogHeight(x) ≪ 1 + ‖H(z a⁺)‖` converts `(1 + ‖Y‖)^{-k}` into
`adelicLogHeight(x)^{-k}`. It is a bound for the *raw* height of `x`, not for a quotient
height, and it is proved as follows:

- `x = (z a⁺) c` with `c` in a compact set. The matrix-and-inverse norm is submultiplicative
  up to a fixed scalar (the Library's `adelicHeight_mul_le`, where `adelicHeight` is a fixed
  multiple of `adelicSourceNorm`). Hence `log ‖x‖_ρ ≤ log ‖z a⁺‖_ρ + C`.
- `log ‖z a⁺‖_ρ ≪ 1 + ‖H(z a⁺)‖`: `ρ` restricted to the split torus is diagonalized by a
  rational matrix, and the diagonal entries of the image of `z a⁺` and of its inverse are
  characters evaluated at archimedean places.
- Equivalently, apply Delorme (2.8) (`σ ∼ 1 + ‖H₀‖` on a standard Siegel domain) to the
  chamber representative, then bound the right translation by a compact set by
  submultiplicativity.

Lapid's property 4 concerns his quotient function `σ_L` and is not used for the raw height.

Items 1 and 2 are part of `Θ ∈ 𝒞([G]) ⊆ C^∞([G])`. The `E j` of `IsWavePacket` agree with
the Eisenstein series for sufficiently regular parameters and are meromorphic and
holomorphic on `D ⊇ i𝔞_P^*`. By uniqueness of meromorphic continuation they are the
continued Eisenstein series there, which are left `G(F)`-invariant and continuous in `g`
locally uniformly in `λ`. Delorme works with standard `P ⊇ P₀` and `K` in good position.
Three steps reduce item 3 to his setting:

- the `G(F)`-conjugacy of pairs (minimal parabolic, maximal split torus) (Borel–Tits),
  together with item 2, gives arbitrary setups `(T, i, ν)`;
- rational conjugation gives non-standard `P`, and the compact-subgroup comparison gives
  other `K`; these are the transfers described in "Non-standard parabolics" of
  `AdelicWavePacketCompletenessReduction.md`;
- an arbitrary compact subgroup in `C` and an arbitrary compact `Ω` are covered because
  (5.2) holds for every compact `Ω`.

These transfers are part of the proof obligation of the statement. On a covering Siegel
domain (2.3), item 3 gives `|Θ| ≪_n σ^{-n} e^{ρ(H₀)}`. By (2.8) and Lemma 2.1 (i), this
bound is comparable to the `u = 1` case of the defining estimates of `𝒞([G])`.
Derivatives `R_u Θ` are not stated.

### `SiegelDominatedIntegrabilityStatement`

Let `F` be a number field, `G` connected reductive and `rho` closed
(`IsClosedSubgroup rho`). Then there exist:

- an algebraic Siegel setup `(T, i, ν, T₀, j)`;
- compact factors `C`, a threshold `t` and a compact `Ω`;
- `d : ℕ`,

such that the following holds. Let `f : G(𝔸) → [0, ∞]` be measurable and left
`G(F)`-invariant with

`f(x) ≤ siegelModulus(a) / adelicLogHeight(x)^d`

at every Siegel point `x` with torus coordinate `a`. Then
`∫⁻ y, f(y.out) ∂μG < ∞`, where
`μG = LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G) … Measure.haar` is the
measure of the target.

*The hypothesis on `f`.* A point `x` may have several factorizations with different torus
coordinates `a`, and the hypothesis is required for each of them. So `f(x)` must lie below
the infimum of the bounds `siegelModulus(a) / adelicLogHeight(x)^d` over all admissible torus
coordinates `a` of `x`. For example, take `SL₂` with `Ω = {1, a₀}` for a positive torus
element `a₀` of modulus `> 1`, threshold `1` and identity prefix factors. The point
`x = a₀` has the coordinates `a = a₀` (with `w = 1`) and `a = 1` (with `w = a₀`), whose
weights differ. The derivation below uses the bound for one factorization only.

*Provenance (derived; neither Lapid nor Delorme states this proposition).* It is derived
from Lapid's §1–2, quoted by Delorme as (2.5). Lapid's statements used are:

- his domain `𝔰 = {g ∈ G(𝔸) : H(g) ∈ T₁ + 𝔞₀⁺} = P₀(𝔸)¹ e^{T₁ + 𝔞₀⁺} K` is open and left
  `P₀(F)`-invariant, with `G(F) 𝔰 = G(𝔸)`;
- (2): `∫_{G(F)\G(𝔸)} f ≤ ∫_{P₀(F)\𝔰} f` for every nonnegative measurable `f` on
  `G(F)\G(𝔸)`. The right side is an integral over the quotient `P₀(F)\𝔰`, not over `𝔰`.
  An integral over `𝔰` itself can be infinite here. For example, for `G = G_m` over `ℚ`
  there are no roots, so `𝔰 = G(𝔸)`, and `σ_L^{-d}` with `d > 1` is integrable on the
  quotient but not on `G(𝔸)`;
- (3): `𝔰 ⊆ P₀(F) e^{T₁ + 𝔞₀⁺} Ω_L` for a compact `Ω_L = Ω₀ K` with `Ω₀ ⊆ P₀(𝔸)¹`;
- property 2: `σ_L(y) ≤ 1 + ‖H(y)‖` for `y ∈ 𝔰`;
- (5): `Ξ σ_L^{-n} ∈ L²(P₀(F)\𝔰)` for `n > r/2`, where `r` is the `F`-rank of `G`.

*Choice of data.* Take an algebraic Siegel setup `(T, i, ν, T₀, j)` whose standard minimal
parabolic is Lapid's `P₀` and whose maximal split torus `i : T → G` is Lapid's maximal split
torus of `G` (Lapid's `T₀`; the setup's own `T₀` is its part in the derived group). Take `Ω_N = {1}`, `Ω_M = {1}`, any
compact subgroup, and a threshold `t ≤ min_β e^{⟨β, T₁⟩}` over the simple roots `β`. Then
`|β(e^X)| ≥ t` for `X ∈ T₁ + 𝔞₀⁺`. Take `Ω = Ω_L` and an even `d = 2n > r`.

*Compact-prefix representatives.* Let `y ∈ 𝔰`. By (3), `y = p x` with `p ∈ P₀(F)` and
`x = e^X ω`, where `X ∈ T₁ + 𝔞₀⁺` and `ω = ω₀ k ∈ Ω_L`. Write `e^X = z a` with
`z = e^{X_G} ∈ A_G` and `a ∈ A_{T₀}`, as in "Definitions". Then `x = z a ω` is a Siegel point
for the chosen data, with torus coordinate `a`, central factor `z`, `n = m = 1`, `k = 1` and
`w = ω`; the threshold holds because `|β(a)| = |β(e^X)| = e^{⟨β, X⟩} ≥ t`. The central factor
cannot be dropped: for `G = G_m` over `ℚ` the torus `T₀` is trivial and the points `a ω` all
have idele norm one, while by the product formula the `P₀(ℚ)`-orbit of a point of `𝔰` of idele
norm `2` contains no point of norm one.
Moreover:

- `f(y) = f(x)`, by left invariance;
- `H(y) = H(x) = X`. Indeed `H` is left `P₀(F)`-invariant, and
  `e^X ω₀ e^{-X} ∈ P₀(𝔸)¹`. Hence `siegelModulus(a) = δ_{P₀}(a) = δ_{P₀}(e^X) = Ξ(y)²`, since
  `δ_{P₀}(z) = 1` for the central `z`;
- `σ_L(y) ≪ adelicLogHeight(x)`. This compares the raw height of the representative `x`
  with Lapid's quotient `σ_L`. By property 2, `σ_L(y) ≤ 1 + ‖X‖`. Next,
  `‖X‖ ≪ 1 + log ‖e^X‖_ρ`, because `ρ` is a closed embedding: its weights on the split
  torus span `𝔞₀^*`, and the matrix-and-inverse norm of `e^X` is at least
  `e^{|⟨λ, X⟩|}` for each weight `λ`, up to the norm of a rational diagonalizing matrix.
  Finally, `log ‖e^X‖_ρ ≤ log ‖x‖_ρ + C`, by submultiplicativity, since `ω⁻¹` ranges over a
  compact set.

The hypothesis for this factorization of `x` therefore gives `f(y) ≪ Ξ(y)² σ_L(y)^{-d}` on
`𝔰`. By (2) and (5),

`∫_{[G]} f ≤ ∫_{P₀(F)\𝔰} f ≪ ∫_{P₀(F)\𝔰} Ξ² σ_L^{-2n} < ∞`.

Lapid's Haar measure and the `Measure.haar` underlying `μG` differ by a positive constant.

Other choices of data are possible, since the statement is existential in them. For example,
the Library's cover `exists_rational_mul_mem_weakSiegelProduct_mul`
(`Langlands/Global/AdelicFiniteVolumeProof.lean`) of `G(𝔸)¹` uses a finite right factor.
With such a cover, the comparison of torus coordinates with Lapid's `H` and of
`adelicLogHeight` with `σ_L` must be redone.

The closedness of `rho` is what makes `adelicLogHeight` grow along the torus. Without it the
statement fails: for `rho` trivial, `adelicLogHeight ≡ 1`. An invariant function on `SL₂`
comparable to `δ` in the cusp and zero elsewhere then satisfies the hypothesis, but its
integral over `[G]` is infinite.

The two statements together replace Delorme's route through
`Ξ^{[G]}(x) = vol_{[G]}(xB)^{-1/2}` ((2.9)) and (2.10). The comparison of Lemma 2.1 (i)
between `Ξ^{[G]}` and `e^{ρ(H₀)}` is not needed, and `Ξ^{[G]}` is not defined here.

## The proof of `wavePacketRapidDecay_of_siegel`

Fix the data of the target, a wave packet `Θ` and `m : ℕ`.

1. `hint` applied to `F, G, rho` gives Siegel data and `e : ℕ`. `hdecay` gives continuity,
   `G(F)`-invariance, and, with the same Siegel data and `n = m + e`, a constant `B`.
2. *Measurability.* The measurable space of `[G]` is the quotient σ-algebra
   (`measurable_from_quotient`). By `out_mk_eq_rational_mul`, the chosen representative of
   `G(F) g` is `q g` with `q ∈ G(F)`. Hence `y ↦ Θ(y.out)` pulls back to `Θ`, which is
   continuous. `rationalLogHeight` pulls back to `g ↦ 1 + log max(1, inf_{q ∈ G(F)} ‖q g‖_ρ)`:
   the infimum is reindexed by right multiplication on `G(F)` (`Equiv.iInf_congr`). This is a
   countable infimum of measurable functions (`measurable_rationalLogHeight`): `G(F)` is
   countable because it is discrete (`LeftCosetSpace.countable_of_isDiscrete`), and
   `‖·‖_ρ` is continuous (`continuous_adelicSourceNorm`). Continuity of `‖·‖_ρ` comes from the
   Library's `continuous_adelicHeight` for `N > 0`; for `N = 0`, `GL_0(𝔸)` is trivial.
   So `y ↦ Θ(y.out) σ_{[G]}(y)^m` is strongly measurable.
3. *The dominated function.* Put
   `f(g) = ((‖Θ g‖ · σ_{[G]}(G(F) g)^m)² / (B² + 1))`, an extended nonnegative real. It is
   measurable (by continuity of `Θ` and step 2) and left `G(F)`-invariant. At a Siegel point `x` with torus coordinate `a` we have:
   - `1 ≤ σ_{[G]}(G(F) x) ≤ adelicLogHeight(x)`, since the infimum is at most the value at
     `x` (`rationalLogHeight_mk_le`, `one_le_rationalLogHeight`);
   - `siegelModulus(a) ≥ 0`;
   - `‖Θ x‖ ≤ B δ^{1/2} / σ(x)^{m+e}`.

   The real inequality `sq_div_le_of_siegel_bound` gives `f(x) ≤ δ(a) / σ(x)^e`. So `hint`
   yields `∫⁻ f(y.out) dμG < ∞`.
4. *Conclusion.* Since `G(F) (y.out) = y`, `‖Θ(y.out) σ_{[G]}(y)^m‖² = (B² + 1) f(y.out)`.
   Hence `∫⁻ ‖Θ(y.out) σ_{[G]}(y)^m‖² dμG < ∞`, and `memLp_two_iff_integrable_sq_norm`
   gives the target's `MemLp … 2 μG`.

The helper lemmas `out_mk_eq_rational_mul`, `continuous_adelicSourceNorm`,
`one_le_adelicLogHeight`, `one_le_rationalLogHeight`, `rationalLogHeight_mk_le`,
`measurable_rationalLogHeight` and `sq_div_le_of_siegel_bound` are proved in the module. The
proof uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## What is not proved here

- `WavePacketSiegelDecayStatement`: the analytic content of Delorme §§3–5 (Proposition 4.1,
  Lemmas 3.1 and 5.1–5.3, the induction of Proposition 5.4), with the transfers to arbitrary
  presented parabolics, compact subgroups and Siegel setups. It also needs the
  identification of `E j` with the continued Eisenstein series, which rests on the Library
  statements `EisensteinMeromorphicContinuationStatement`, `EisensteinConstantTermStatement`
  and `EisensteinImaginaryAxisHolomorphyStatement`, whose proofs are open.
- `SiegelDominatedIntegrabilityStatement`: Lapid's (2), (3) and (5), together with the
  comparison of `adelicLogHeight` on compact-prefix representatives with `σ_L`, all
  formalized for the Library's notions.
- Nothing about `Ξ^{[G]}`, (2.10) or derivatives `R_u Θ` is stated or used.
