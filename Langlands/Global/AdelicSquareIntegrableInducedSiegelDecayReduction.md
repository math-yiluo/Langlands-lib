# The Levi Schwartz estimate for `A^2_P` from Siegel-set decay

Module `Langlands.Global.AdelicSquareIntegrableInducedSiegelDecayReduction`, namespace
`Langlands.Global`.

The module states one proposition, `SquareIntegrableInducedFormSiegelDecayStatement`, and proves

```
theorem squareIntegrableInducedFormLeviSchwartz_of_siegelDecay
    (hdecay : SquareIntegrableInducedFormSiegelDecayStatement) :
    SquareIntegrableInducedFormLeviSchwartzStatement
```

The proposition is not proved here, so the theorem is a reduction: it does not prove
`SquareIntegrableInducedFormLeviSchwartzStatement` (module
`Langlands.Global.AdelicWeakConstantTermLeviEstimates`) unconditionally. That statement and the
notions it uses are unchanged. The theorem uses only the axioms `propext`, `Classical.choice`
and `Quot.sound`.

## Sources

- P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered
  as `delorme-2023-spectral-theorem-langlands` (published PDF, SHA-256
  `9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`): §2, p. 7, Siegel
  domains (2.3); p. 8, the height `σ(g) = 1 + log ‖g‖` with (2.7)–(2.8), the function
  `Ξ^{[G]}`, Lemma 2.1 (`Ξ^{[G]} ∼ e^{ρ(H₀)}` and `σ ∼ 1 + ‖H₀‖` on a Siegel domain) and (2.10);
  p. 9, the Schwartz space `𝒞([G])` of smooth `φ` with
  `|R_u φ(x)| ≪ σ_{[G]}(x)^{-n} Ξ^{[G]}(x)` for all `n`; §3.4, p. 15: `𝒜^2(G) ⊂ 𝒞(G)` "from
  [MW], Lemmas I.4.1 and I.4.11".
- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`:
  - I.2.17, pp. 37–38 (chapter file
    `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`): for `φ` on
    `U(𝔸) M(F) \ G(𝔸)` and `k ∈ K`, the slice `φ_k(m) = m^{-ρ_P} φ(m k)` on `M(F) \ M(𝔸)`;
    `φ` is automorphic if and only if it is smooth, `K`-finite and every `φ_k` is automorphic
    (the finiteness under the centre of the enveloping algebra passes to `M` through the
    Harish-Chandra homomorphism);
  - I.3.2, pp. 41–43 (chapter file `05.3_pp_40_48_Cuspidal_components.pdf`): an automorphic
    form is finite under the centre `Z_M` of `M(𝔸)`, and one invariant under `A_M` is a finite
    sum of automorphic forms with central characters, by Fourier inversion on the compact group
    `Z_M(F) A_M \ Z_M(𝔸)`;
  - I.4.1, p. 49 (chapter file
    `05.4_pp_49_77_Upper_bounds_as_functions_of_the_constant_term.pdf`): on a Siegel set an
    automorphic form is bounded by
    `∑ m_{P₀}(g)^{Re π + μ^{M_Q} + ρ_Q} (1 + ‖log m_Q(g)‖)^D` over its cuspidal data, for every
    auxiliary `μ`, where `μ^{M_Q}` is the projection of `μ` to the part orthogonal to
    `𝔞_Q^*`;
  - I.4.11, pp. 74–76 (same chapter file): an automorphic form with unitary central character
    is square integrable if and only if every `Re π` in its cuspidal support along a standard
    parabolic `Q` is `∑_{α ∈ Δ_Q} x_α α` with all `x_α < 0`, equivalently
    `⟨ϖ_α, Re π⟩ < 0` for the fundamental coweights `ϖ_α`, `α ∈ Δ_Q` (Remark (b)); the
    sufficiency part of the proof turns this, through the auxiliary `μ` of I.4.1, into decay
    on Siegel sets.

## `SquareIntegrableInducedFormSiegelDecayStatement`

Hypotheses: exactly those of `SquareIntegrableInducedFormLeviSchwartzStatement` before its
quantifier on `n`. These are a number field `F`, a connected reductive `G`, a subgroup `K` with
`IsMaximalCompactSubgroup F G K`, a closed matrix embedding `rho`, `hsmooth` and `hcalc`, a
compatible family `𝓕` of standard parabolics with `hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K`, a
standard index `J`, and `φ` with
`IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc (𝓕.p J) (𝓕.iU J) (𝓕.l J) φ`.

Conclusion: for every algebraic Siegel setup `(T, i, ν, T₀, j)` of the Levi subgroup
`M = 𝓕.M J` (`IsSiegelAlgebraicSetup F M T i ν T₀ j`), compact factors `C` with an arbitrary
compact subgroup, threshold `t`, compact `Ω ⊆ M(𝔸)` and `n : ℕ`, there is `B` such that

`‖φ(ι(x) k)‖ ≤ B · siegelModulus(a)^{1/2} / σ_M(x)^n`

for every `a`, every `x ∈ M(𝔸)` with `IsSiegelPoint F M T i ν T₀ j C t Ω a x` and
`x ∈ M(𝔸)^1` (`normOneSubgroup F M`), and every `k ∈ K`. Here
`ι = map F M G (𝓕.l J ≫ 𝓕.p J)`, `siegelModulus(a) = δ_{P₀^M}(a)` is the modulus of the minimal
parabolic of the setup at the torus coordinate `a`, and
`σ_M = adelicLogHeight F M (rho.restrict (𝓕.l J ≫ 𝓕.p J))`, the height of the point `x`
itself for `rho` restricted along `M → P → G`. The points are those of the Siegel set
`A_M · Ω_N Ω_M A_{T₀}(t) K_C · Ω` of `M`, as in `IsSiegelPoint`
(`AdelicWavePacketRapidDecaySiegelReduction.md`), intersected with `M(𝔸)^1`.

*Provenance (derived from Delorme §3.4 and Mœglin–Waldspurger I.2.17, I.3.2, I.4.1 and I.4.11
for `M`).* For `k ∈ K` put `f_k(m) = δ_P(m)^{-1/2} φ(ι(m) k)` on `M(𝔸)`. This is the slice
`φ_k(m) = m^{-ρ_P} φ(m k)` of I.2.17, since `m^{ρ_P} = δ_P(m)^{1/2}`. The modulus `δ_P` is the
idele norm of the rational character `det(Ad | Lie U)` of `M`, so it equals `1` on `M(𝔸)^1`, and
`f_k(x) = φ(ι(x) k)` at every point `x ∈ M(𝔸)^1` where the conclusion is evaluated. The bound is
obtained for the normalized slices `f_k` as follows.

1. *Automorphy.* The first condition of `IsSquareIntegrableInducedForm` makes `φ` an
   automorphic form on `U(𝔸) M(F) \ G(𝔸)`, so by I.2.17 every `f_k` is an automorphic form on
   `M(F) \ M(𝔸)`. Since `φ` is finite under `K ∩ G(F_∞)` and smooth, its right translates by
   `K` span a finite-dimensional space. Hence the span `V` of the `f_k`, `k ∈ K`, is a
   finite-dimensional space of automorphic forms on `M`, and `k ↦ f_k` is continuous into `V`.
2. *Unitary central characters.* The `A^n_P` condition `φ(a g) = δ_P(a)^{1/2} φ(g)` for
   `a ∈ A_M` (`IsSplitComponentEquivariant`) makes every `f_k` invariant under `A_M`. By I.3.2
   every `f ∈ V` is a finite sum `∑_ξ f_ξ` of automorphic forms with central characters `ξ`
   of `Z_M(𝔸)`, obtained by Fourier inversion on the compact abelian group
   `C = Z_M(F) A_M \ Z_M(𝔸)`: `f_ξ(m) = ∫_C ξ(c)^{-1} f(c m) dc`. The characters `ξ` are
   trivial on `Z_M(F) A_M`, hence unitary, and finitely many of them occur for all of `V`.
3. *Square integrability.* The last condition of `IsSquareIntegrableInducedForm` says
   `∫_K ∫_{A_M M(F) \ M(𝔸)} |f_k(m)|² dm dk < ∞`. So `f_k` is square integrable for almost
   every `k`. The set of `k` with square-integrable `f_k` is the preimage of a linear subspace
   of `V` under the continuous map `k ↦ f_k`, hence closed. A closed conull subset of `K` is all
   of `K`, since Haar measure charges every nonempty open subset. Translation by a central
   element preserves the `L²` norm on `A_M M(F) \ M(𝔸)`, so every component `f_{k,ξ}` is
   square integrable as well.
4. *Exponents and decay.* For each component `f_{k,ξ}`, I.4.11 for `M` gives
   `⟨ϖ_α, Re π⟩ < 0` for every standard parabolic `Q` of `M`, every `π` in the cuspidal support
   of `f_{k,ξ}` along `Q` and every `α ∈ Δ_Q^M`. Write `ρ₀ = ρ_{P₀^M}`, so that
   `m_{P₀}^{ρ₀} = δ_{P₀^M}^{1/2}`, and `ρ_Q = ρ_Q^M`. Put `λ = Re π + μ^{M_Q} + ρ_Q - ρ₀`. For
   a simple root `α` of `M` outside `M_Q` we have `⟨ϖ_α, λ⟩ = ⟨ϖ_α, Re π⟩ < 0`, because
   `ρ₀ - ρ_Q = ρ₀^{M_Q}` and `μ^{M_Q}` vanish on `ϖ_α ∈ 𝔞_Q`. For a simple root `α` of `M_Q`,
   the auxiliary `μ` can be chosen with `⟨ϖ_α, λ⟩ < 0`, as in the sufficiency part of the
   proof of I.4.11. On a Siegel set of `M`, `α(H₀) ≥ t₀` for every simple root `α`. On
   `M(𝔸)^1` the `𝔞_M`-component of `H₀` vanishes, so `H₀ = ∑_α α(H₀) ϖ_α` and
   `m_{P₀}^{λ} ≤ C e^{-ε ‖H₀‖}`. This absorbs the polynomial factor of I.4.1. The second bound
   of I.4.1 for `M` therefore gives `|f_{k,ξ}| ≪_n δ_{P₀^M}^{1/2} (1 + ‖H₀‖)^{-n}` on the norm-one
   points of the Siegel set. By Delorme (2.8) and Lemma 2.1, `σ_M ≪ 1 + ‖H₀‖` there. Summing over
   the finitely many `ξ` gives the bound for each `f_k`. Apply it to a basis of `V` chosen among
   the `f_k`. Every `f_k` is a combination of this basis with coefficients continuous in `k`,
   hence bounded on the compact `K`, so the bound is uniform in `k`.
5. *General Siegel data.* Arbitrary setups, compact factors and compact `Ω` reduce to these
   Siegel sets by rational conjugacy of minimal parabolic pairs and by compact right
   translation, as described for `WavePacketSiegelDecayStatement`.

The sources take `K` in good position. Here `K` is any maximal compact subgroup with
`P_∅(𝔸) K = G(𝔸)`, with `A^2_P` defined for this `K`. Right translation by an archimedean
element `g` with `g (K ∩ G(F_∞)) g⁻¹` in good position turns a form in `A^2_P` for `K` into a
form finite under the conjugate compact subgroup (finiteness at the finite places follows from
smoothness), and the bound is stable under compact right translation. Handling general `K` in
this way is part of the proof of the proposition. By (2.8) and Lemma 2.1 of Delorme, the bound
is the `u = 1` case of the defining estimates of `𝒞([M]^1)`, written on Siegel sets.

## Proof of `squareIntegrableInducedFormLeviSchwartz_of_siegelDecay`

Fix the data of `SquareIntegrableInducedFormLeviSchwartzStatement`, `φ ∈ A^2_P` and `n`. Write
`M = 𝓕.M J`, `ι = map F M G (𝓕.l J ≫ 𝓕.p J)`, `ρ_M = rho.restrict (𝓕.l J ≫ 𝓕.p J)`,
`μ_K = compactHaarProbability F G K` and `μ₁ = normOneRationalQuotientHaarMeasure F M`. The
target measure `𝓕.squareIntegrablePairingMeasure K hK.isCompact J` is `μ_K × μ₁` by definition.

1. **The Levi.** `M` is connected reductive (`(𝓕.isCompatible J).levi.isConnectedReductive`)
   and `ρ_M` is closed, as the composite of the closed immersions `M → P → G` with `rho`.
2. **Data.** `normOneSiegelDecayIntegrability` (module
   `Langlands.Global.AdelicNormOneSiegelDominatedIntegrability`) applied to `M` and `ρ_M`
   gives Siegel data of `M` and `e : ℕ`. The hypothesis `hdecay` with these data and the
   exponent `n + e` gives `B`.
3. **Properties of `φ`.** `φ` is continuous (part of `IsAdelicSmoothFunction`) and invariant
   under left translation by `U(𝔸) M(F)`. In particular `φ(ι(q) g) = φ(g)` for `q ∈ M(F)`
   (`InducedInnerProductIntegrable.map_map_mem_parabolicQuotientSubgroup`, with
   `InducedInnerProductIntegrable.map_comp_apply`).
4. **Measurability.** Put `σ̄(x) = rationalLogHeight F M ρ_M (M(F) x)`, a measurable function
   on `M(𝔸)` with `σ̄ ≥ 1`, invariant under `M(F)`. On `K × M(F) \ M(𝔸)^1` the weight of the
   target is `σ̄(y.out)`, because the class of `y` in `M(F) \ M(𝔸)` is that of `y.out`
   (`Quotient.out_eq`, `normOneQuotientInclusion_mk`). The factor
   `z ↦ φ(ι(z₂.out) z₁)` is continuous, by `LeftCosetSpace.continuous_out_of_invariant` and step 3.
   The weight factor is measurable (`measurable_rationalLogHeight`,
   `continuous_normOneQuotientInclusion`). So the target function `g` is a.e. strongly
   measurable, and by `memLp_two_iff_integrable_sq_norm` it remains to bound
   `∫⁻ ‖g‖² d(μ_K × μ₁)`.
5. **The dominated function.** On `M(𝔸)` put

   `f(x) = ∫_K (‖φ(ι(x) k)‖ σ̄(x)^n)² / (B² + 1) dμ_K(k)`.

   It is measurable, because the integrand is jointly measurable on `M(𝔸) × K`
   (`Measurable.lintegral_prod_right'`). It is left `M(F)`-invariant by step 3 and the
   invariance of `σ̄`. At a norm-one Siegel point `x` with torus coordinate `a`, step 2 gives
   `‖φ(ι(x) k)‖ ≤ B δ(a)^{1/2} / σ_M(x)^{n+e}` for every `k ∈ K`. With
   `1 ≤ σ̄(x) ≤ σ_M(x)` (`one_le_rationalLogHeight`, `rationalLogHeight_mk_le`) and
   `δ(a) ≥ 0`, the inequality `sq_div_le_of_siegel_bound` bounds the integrand by
   `δ(a) / σ_M(x)^e`. Since `μ_K` is a probability measure, `f(x) ≤ δ(a) / σ_M(x)^e`. Step 2
   then gives `∫⁻ f(y.out) dμ₁(y) < ∞`.
6. **Conclusion.** For `z = (k, y)` we have `‖g(z)‖ = ‖φ(ι(y.out) k)‖ σ̄(y.out)^n`. By Tonelli
   (`lintegral_prod_symm`),

   `∫⁻ ‖g‖² d(μ_K × μ₁) = (B² + 1) ∫⁻ f(y.out) dμ₁(y) < ∞`.

The hypotheses that `K` is maximal compact in `G(𝔸)` and that `P_∅(𝔸) K = G(𝔸)` enter only
through `hdecay`. The reduction itself uses the compactness of `K`, for the probability
measure `μ_K`.
