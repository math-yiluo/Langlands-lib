# Siegel-set decay of wave packets from joint continuity and the chamber estimate

Module `Langlands.Global.AdelicWavePacketSiegelDecayReduction`, namespace `Langlands.Global`.

The Library's `WavePacketSiegelDecayStatement`
(`Langlands/Global/AdelicWavePacketRapidDecaySiegelReduction.lean`) has three conclusions for
every wave packet `Θ` of `IsWavePacket`:

1. `Θ` is continuous;
2. `Θ(q g) = Θ(g)` for every `q ∈ G(F)`;
3. for every algebraic Siegel setup, all compact factors `C`, every threshold `t`, every compact
   `Ω` and every `n`, there is `B` with `‖Θ x‖ ≤ B · siegelModulus(a)^{1/2} / adelicLogHeight(x)^n`
   at every point `x` of the Siegel set `A_G · Ω_N Ω_M A_{T₀}(t) K_C · Ω` with torus coordinate `a`.

This module states two propositions, `EisensteinImaginaryJointContinuityStatement` and
`WavePacketChamberDecayStatement`, proves conclusion 2 without any hypothesis, and proves

```
theorem wavePacketSiegelDecay_of_reduction
    (hcont : EisensteinImaginaryJointContinuityStatement)
    (hchamber : WavePacketChamberDecayStatement) : WavePacketSiegelDecayStatement
```

Neither proposition is proved here. The theorem is a reduction, not an unconditional proof of
`WavePacketSiegelDecayStatement`.

## Sources

- P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered
  as `delorme-2023-spectral-theorem-langlands` (published PDF numbering). §2, p.7: Siegel
  domains (2.3) and the inclusion (2.4) of a Siegel domain in `Ω_{N_P} exp(𝔞_0^{+,P}) Ω`, proved
  by conjugating the compact factor by `exp(-X)`; p.8: `σ(g) = 1 + log ‖g‖` and (2.8). §5.2,
  pp.20–21: Proposition 5.4 and its proof, in particular the estimate (5.2) and the final
  sentence "As a finite number of `S₀` covers `S⁺` this achieves to prove the proposition".
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`
  (journal PDF). Theorem 2.3 (1) and (6), p.191; the Corollary at the end of §8.6, p.226.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*,
  Clay Math. Proc. 13 (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`. Proposition 6 and its proof,
  printed pp.329–330 (PDF pp.338–339).

## `EisensteinImaginaryJointContinuityStatement`

The data are those of the Library's `EisensteinImaginaryAxisHolomorphyStatement`: a number
field `F : Type`, a connected reductive `G`, a parabolic `p : P → G` with presentation
`r : ParabolicRootPresentation p l a` and geometric unipotent radical `iU`, a maximal compact
subgroup `K` with `hK : IsIwasawaCompact p K`, a closed matrix embedding `rho`, `hsmooth`,
`hcalc`, and `φ ∈ A^2_P` (`IsSquareIntegrableInducedForm`). Let
`E : X^*(P) ⊗ ℂ → G(𝔸) → ℂ` and `D ⊆ X^*(P) ⊗ ℂ` satisfy:

- `D` contains every imaginary parameter `imaginaryParameter F P x`, `x ∈ X^*(P) ⊗ ℝ`;
- for every `g`, `λ ↦ E λ g` is meromorphic in linear coordinates with domain of holomorphy
  `D` (`IsMeromorphicInCoordinatesOn`);
- `E λ = hK.eisensteinSeries φ λ` for `Re λ` sufficiently regular (`r.IsRegularParameter`).

Conclusion: for every `n` and every real linear isomorphism `e : ℝⁿ ≃ X^*(P) ⊗ ℝ`, the map
`(x, g) ↦ E (imaginaryParameter F P (e x)) g` is continuous on `ℝⁿ × G(𝔸)`.

*Provenance (derived).* No source states joint continuity as such. It follows from the
following results.

- Bernstein–Lapid, Corollary of §8.6: near every `λ₀`, the product of `E(φ, λ)` with a power of
  `∏_{β} ⟨λ - λ₀, β^∨⟩` has a convergent power series expansion in a Fréchet space
  `𝔉^R_{sm}(X)` of smooth functions of uniform moderate growth. The Fréchet topology is finer
  than the topology of uniform convergence on compact subsets of `G(𝔸)`.
- Lapid, Proposition 6: for `φ ∈ A^2_P` the Eisenstein series is holomorphic at every point of
  `i𝔞_P^*`. Its proof excludes a factor `⟨λ - λ₀, α^∨⟩^k` with `k ≥ 1` in front of the
  Fréchet-valued series, and it uses the resulting continuity of `E*(x, λ)` in `x`, uniformly
  for `λ` near `λ₀` (printed p.330).

So near every `λ₀ ∈ i𝔞_P^*` the continued series is a holomorphic, in particular continuous,
map into a space whose topology controls uniform convergence on compact sets of `G(𝔸)`, and the
map `(λ, g) ↦ E(φ, λ)(g)` is jointly continuous there. The statement is universal in the
continuation `(E, D)`. Any two such continuations agree on the intersection of their domains,
by uniqueness of meromorphic continuation from the nonempty open regular region
(`ParabolicRootPresentation.eqOn_of_regularParameter`,
`Langlands/Global/AdelicWavePacketRationalInvariance.lean`). The imaginary parameters lie in
both domains, so the values `E (i e(x)) g` are those of the continued series.

## `WavePacketChamberDecayStatement`

The hypotheses are those of `WavePacketSiegelDecayStatement`: `F`, a connected reductive `G`, a
maximal compact `K`, a closed matrix embedding `rho`, `hsmooth`, `hcalc`, a minimal parabolic
`p₀` with `IsIwasawaCompact p₀ K`, and a wave packet `Θ` (`IsWavePacket F G K rho hsmooth hcalc
Θ`). Conclusion: for every algebraic Siegel setup `(T, i, ν, T₀, j)`
(`IsSiegelAlgebraicSetup`), every threshold `t : ℝ≥0ˣ`, every compact `Ω ⊆ G(𝔸)` and every
`n : ℕ` there is `B : ℝ` such that

`‖Θ(z · a · ω)‖ ≤ B · siegelModulus(a)^{1/2} / adelicLogHeight(z · a · ω)^n`

for every `z ∈ A_G` (`RestrictionSplitCentre.canonicalSubgroup F G`), every `a` in the weak
simple-root chamber `PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t`, mapped into
`G(𝔸)` by `positiveMap`, and every `ω ∈ Ω`.

These are the points of `IsSiegelPoint` with trivial compact prefix (`Ω_N = Ω_M = {1}`), with the
compact subgroup absorbed into `Ω`.

*Provenance (derived from Delorme's proof of Proposition 5.4).* The estimate (5.2) reads
`|E_a(exp X_G exp(tX) ω)| ≪_k (1 + ‖X_G‖)^{-k} (1 + t)^{-k} e^{tρ(X)}` for `X_G ∈ 𝔞_G`, `t > 0`,
`X` in a neighbourhood `S₀` of a point of the unit sphere `S⁺` of `𝔞_0^{G,+}`, and `ω` in an
arbitrary compact `Ω`. Finitely many `S₀` cover `S⁺`. Hence
`|E_a(exp X_G exp Y ω)| ≪_k (1 + ‖X_G‖)^{-k} (1 + ‖Y‖)^{-k} e^{ρ(Y)}` for `Y ∈ 𝔞_0^{G,+}`.
The translation to the present form is as follows.

- `z = exp X_G`.
- The torus coordinate `a` corresponds to `exp Y`, and `siegelModulus(a)^{1/2} = e^{ρ(Y)}`, as
  explained in `Langlands/Global/AdelicWavePacketRapidDecaySiegelReduction.md`.
- For a threshold `t ≠ 1`, a point of the chamber `|β(a)| ≥ t` is a point of the closed chamber
  times a point of a compact box, which commutes with `a` and is absorbed into `Ω`. The modulus
  changes by a bounded factor.
- `adelicLogHeight(z a ω) ≪ 1 + ‖X_G‖ + ‖Y‖`, by (2.8) together with the submultiplicativity of
  the height under right translation by the compact `Ω`.

Delorme works with standard parabolics containing a fixed minimal parabolic and with a compact
subgroup in good position. The statement quantifies over every presented parabolic `P` with
`P(𝔸)K = G(𝔸)`, every maximal compact `K` with an Iwasawa decomposition for some minimal
parabolic, and every algebraic Siegel setup. The transfers from Delorme's setting are therefore
part of the proof obligation of this statement:

- through the `G(F)`-conjugacy of pairs (minimal parabolic, maximal split torus) and the left
  `G(F)`-invariance of `Θ`, to arbitrary setups;
- through rational conjugation, to non-standard parabolics, as in "Non-standard parabolics" of
  `Langlands/Global/AdelicWavePacketCompletenessReduction.md`;
- through the comparison of compact subgroups, to the given `K`.

## The proofs

### Conclusion 2: `IsWavePacket.leftRationalInvariant`

Unpack `IsWavePacket`. Every `v j` is left invariant under `P(F) U(𝔸)`, the first clause of
`IsSquareIntegrableInducedForm`. By the Library's `eisensteinContinuation_leftRationalInvariant`,
each `E j λ` is then left `G(F)`-invariant for every `λ ∈ D`. Its proof reindexes the defining
sum and propagates the identity from the regular region by uniqueness of meromorphic
continuation. The packet integrates `E j` only at the imaginary parameters `i e(x) ∈ D`. So the
Library's `packetIntegral_leftRationalInvariant` gives `Θ(q g) = Θ(g)`. No hypothesis beyond
`IsWavePacket` and the connected reductivity of `G` is used.

### Conclusion 1: `IsWavePacket.continuous_of_jointContinuity`

`Θ(g) = ∫ f(g, x) dμ(x)`, with `f(g, x) = ∑ j, c j x · E j (i e(x)) g` and `μ = spectralMeasure n`.

- `EisensteinImaginaryJointContinuityStatement`, applied to each `(v j, E j, D)` with the
  coordinates `e`, makes `f` jointly continuous; the coefficients `c j` are smooth.
- `f(g, x) = 0` for `x` outside the compact set `s = ⋃ j, tsupport (c j)`.
- `μ` is finite on compact sets (`IsFiniteMeasureOnCompacts.smul`), because
  `μ = (2π)^{-n} · volume`.

The auxiliary theorem `continuous_integral_of_forall_notMem_eq_zero` then gives continuity. Its
proof does not need first countability of `G(𝔸)`. The integral equals the integral over `s`.
`IsCompact.mem_uniformity_of_prod` gives, for every `δ > 0`, a neighbourhood of `g₀` on which
`‖f(g, x) - f(g₀, x)‖ ≤ δ` for all `x ∈ s`. The difference of the integrals is then at most
`δ · μ(s)` (`norm_setIntegral_le_of_norm_le_const`).

### Conclusion 3: `siegelPoint_bound_of_chamber_bound`

This is Delorme's (2.4) argument in the present setting. Let `x = z · (n m a k) · w` be a point
of the Siegel set. Put `A = positiveMap a`.

- The standard Levi of the setup is the centralizer of the torus (a clause of
  `IsSiegelAlgebraicSetup`). So `m` commutes with `A`
  (`commute_of_mem_standardLevi_image`). Hence `x = z · A · ω` with
  `ω = (A⁻¹ n A) · m · k · w`.
- `exists_isCompact_conj_unipotent`: there is a compact `S` containing `A⁻¹ n A` for all
  `n ∈ Ω_N` and all `a` in the chamber. For `N > 0` the heights of these points are bounded
  (the Library's `exists_adelicHeight_conj_unipotent_le`), and height sublevels of a closed
  embedding are compact (`isCompact_adelicHeightSublevel`). For `N = 0`, a closed embedding
  forces `G(𝔸)` to be a single point (`isClosedEmbedding_adelicMatrix`).
- So `ω` lies in the compact set `Ω' = S · ι(Ω_M) · K_C · Ω`.

`WavePacketChamberDecayStatement` for `Ω'` gives `B` with
`‖Θ x‖ = ‖Θ(z A ω)‖ ≤ B · siegelModulus(a)^{1/2} / adelicLogHeight(x)^n`, the height being taken
at the same point `x`.

### Assembly

`wavePacketSiegelDecay_of_reduction` combines the three conclusions.

## What is not proved here

- `EisensteinImaginaryJointContinuityStatement`. It needs the Fréchet-valued meromorphic
  continuation of Eisenstein series and its holomorphy near `i𝔞_P^*` (Bernstein–Lapid,
  Lapid).
- `WavePacketChamberDecayStatement`: the analytic content of Delorme §§3–5 (uniform
  temperedness, Proposition 4.1; Lemmas 5.1–5.3; the weak constant term (4.3); the induction on
  `dim 𝔞_0^G`), with the comparison `adelicLogHeight ≪ 1 + ‖H‖` and the transfers listed above.
