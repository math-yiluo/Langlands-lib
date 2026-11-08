# Poisson summation over a number field for tensor test functions

Module `Langlands.Global.Hecke.AdelicPoisson`, namespace `Langlands.Global.Hecke`.

Throughout, `K` is a number field, `FinitePlace K` its finite places, `K_v = FiniteCompletion K v`
the completions with the local-field data `topologicalData v`, `L_v(k)` the valuation lattice
`π_v^{-k} O_v = (topologicalData v).additiveLattice k`, and `ι = mixedEmbedding K : K → V` the
embedding into the mixed space `V = mixedSpace K` with Lebesgue measure and norm
`N = mixedEmbedding.norm`. For a unit fractional ideal `I`, `idealLattice K I = ι(I)`, and for a
finitely supported `m : FinitePlace K →₀ ℤ`, `latticeIdeal m = ∏ 𝔭_v^{-m v}` (from
`Langlands.Global.Hecke.AdelicLattice`). The archimedean scales `aR, aC` give
`T = addTrace aR aC`, `T(x) = Σ aR_v x_v + Σ 2 Re(aC_v x_v)`, the bilinear form
`B = tracePairing aR aC`, `B(x, y) = -T(x y)`, Mathlib's Fourier transform
`𝓕F w = VectorFourier.fourierIntegral 𝐞 volume B F w = ∫ 𝐞(T(x w)) F(x) dx`, and
`κ = mixedGaussianConst aR aC = ∏ √|aR_v| ∏ 2 ‖aC_v‖` (from
`Langlands.Global.Hecke.MixedSpaceFourier`). `ψ_v = ψf v` are unitary additive characters of
the `K_v`, `n_v` their additive conductors, `μ_v` self-dual Haar measures, and
`AdditiveProductFormula aR aC ψf` is the additive product formula
`𝐞(T(ι x)) ∏_v ψ_v(x) = 1` for `x ∈ K` (from `AdelicLattice`). `thetaSeries a F y =
∑' γ : K, a γ * F (ι γ * y)` is the theta series of `Langlands.Global.Hecke.ThetaDecay`.

The module proves Poisson summation over `K` for test functions that are tensors of a function
on the mixed space and Schwartz–Bruhat functions at the finite places, in the form needed by the
proof of the Hecke global functional equation: a sum over `K` rather than over the adeles. It is
an internal helper module and states nothing about `L`-functions.

## Provenance

Internal helper for the proof of the published actual Hecke global functional equation
statement. `tsum_tensorCoeff_mul_eq` is the Poisson formula of Tate's thesis, Lemma 4.2.4
(J. T. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in
Cassels–Fröhlich, *Algebraic Number Theory* (1967), p. 333: `Σ_{ξ ∈ k} f̂(ξ) = Σ_{ξ ∈ k} f(ξ)`),
for the adelic test functions `f = F ⊗ ⊗_v g_v` with `g_v = 1_{O_v}` outside `S`, written as a sum
over `K`. `thetaSeries_tensorCoeff_eq` is the corresponding case of Tate's Riemann–Roch theorem,
Theorem 4.2.1 (p. 333: `|a|⁻¹ Σ f̂(ξ/a) = Σ f(a ξ)`), for ideles `a` with trivial finite part,
`|a| = N(y)`. Tate deduces Lemma 4.2.4 from the duality and measure theory of the compact group
`A/k`. Here the proof is different: each `g_v` is expanded into indicators of cosets of one
valuation lattice (the published `padicLatticeSchwartzExpansion`), a tensor of coset indicators
is the indicator of a translate `γ₀ + latticeIdeal m` by strong approximation, and the coset case
is lattice Poisson summation (`tsum_add_zlattice_eq` of
`Langlands.Global.Hecke.LatticePoissonGeneral`) combined with the lattice duality and the
Tamagawa normalization of `AdelicLattice` and the published local formula
`padicLatticeFourier` for the Fourier transform of a coset indicator. The definitions
`IntegralOutside`, `tensorCoeff`, `cosetIndicator`, `dualCosetCoeff` and `localFourier` are
internal encodings chosen for this route.

## Definitions

- `IntegralOutside S γ : Prop`: `γ ∈ L_v(0)` (integral) at every finite place `v ∉ S`.
- `tensorCoeff S g γ = if IntegralOutside S γ then ∏_{v ∈ S} g_v(γ) else 0`, for a finite set
  `S` of finite places and local functions `g v : K_v → ℂ`. When `g_v = 1_{O_v}` for `v ∉ S` this
  is the restriction to `K` of the adelic tensor `⊗_v g_v`.
- `cosetIndicator v a k : K_v → ℂ`, the indicator of the coset `a + L_v(k)` (in the form
  `{z | z - a ∈ L_v(k)}` of the published Schwartz–Bruhat expansion).
- `dualCosetCoeff ψf μ m a v y = μ_v(L_v(m_v)) ψ_v(a_v y) 1_{L_v(n_v - m_v)}(y)`, the local
  Fourier transform of `cosetIndicator v (a v) (m v)` (with `μ_v(L)` the real mass
  `latticeMass`).
- `localFourier ψf μ v g y = HarmonicAnalysis.fourierTransform (ψf v) (μ v).val g y =
  ∫ ψ_v(x y) g(x) dμ_v(x)`, the local Fourier transform of a Schwartz–Bruhat function `g` on `K_v`
  for the self-dual measure `μ_v`, with the Borel σ-algebra of the topology of
  `topologicalData v`.

## Main results

### Sums over ideal lattices

- `mixedEmbedding_mem_idealLattice_iff`: `ι γ ∈ idealLattice K I ↔ γ ∈ I`.
- `indicator_idealLattice_mixedEmbedding`: `1_{ι(I)} f (ι γ) = 1_I (f ∘ ι)(γ)`.
- `indicator_idealLattice_eq_zero_of_notMem_range`: `1_{ι(I)} f` vanishes off `ι(K)`.
- `tsum_indicator_idealLattice`: `∑_{x ∈ V} 1_{ι(I)} f (x) = ∑_{γ ∈ K} 1_I (f ∘ ι)(γ)`.
- `summable_indicator_idealLattice_iff`: the corresponding equivalence of summability.

### Tensor coefficients

- `tensorCoeff_cosetIndicator_eq`: if `m` is supported in `S`, `γ₀ - a_v ∈ L_v(m_v)` for
  `v ∈ S` and `γ₀` is integral outside `S`, then
  `tensorCoeff S (cosetIndicator · (a ·) (m ·)) γ = 1_{latticeIdeal m}(γ - γ₀)`.
- `tensorCoeff_congr`: `tensorCoeff S g` only depends on `g_v` for `v ∈ S`.
- `tensorCoeff_eq_sum`: if `g_v(y) = Σ_{i < N_v} c_{v,i} k_{v,i}(y)` for `v ∈ S`, then
  `tensorCoeff S g γ = Σ_p (∏_{v ∈ S} c_{v, p_v}) tensorCoeff S (k_{·, p_·}) γ`, the sum over all
  choices `p = (p_v)_{v ∈ S}` of indices.

### Poisson summation for tensors of coset indicators

The following assume `aR v ≠ 0`, `aC v ≠ 0`, `AdditiveProductFormula aR aC ψf`, `n_v = n v` for a
finitely supported `n`, self-dual `μ_v`, `supp n ⊆ S` and `supp m ⊆ S`.

- `prod_character_eq_fourierChar`: for `γ₀` as above and `w ∈ latticeIdeal (n - m)`,
  `∏_{v ∈ S} ψ_v(a_v w) = 𝐞(B(ι γ₀, ι w))`.
- `tensorCoeff_dualCoset_eq`: for `γ₀` as above,
  `tensorCoeff S (dualCosetCoeff ψf μ m a) w = (∏_{v ∈ S} μ_v(L_v(m_v))) ·
  1_{latticeIdeal (n - m)}(w) 𝐞(B(ι γ₀, ι w))`.
- `tsum_tensorCoeff_cosetIndicator_mul_eq`: for continuous `F` with
  `‖F x‖ ≤ C (1 + ‖x‖)^{-r}` and `‖𝓕F w‖ ≤ C' (1 + ‖w‖)^{-r}`, `r > [K : ℚ]`,
  `∑_{γ ∈ K} tensorCoeff S (cosetIndicator · (a ·) (m ·)) γ F(ι γ) =
  κ ∑_{w ∈ K} tensorCoeff S (dualCosetCoeff ψf μ m a) w 𝓕F(ι w)`.
- `summable_tensorCoeff_cosetIndicator_mul`, `summable_tensorCoeff_dualCoset_mul`: both series
  are summable.

### Poisson summation for tensors of Schwartz–Bruhat functions

- `localFourier_eq_sum`: if `g(x) = Σ_i c_i 1_{a_i + L_v(m)}(x)`, then
  `localFourier ψf μ v g y = Σ_i c_i μ_v(L_v(m)) ψ_v(a_i y) 1_{L_v(n_v - m)}(y)`.
- `tsum_tensorCoeff_mul_eq` (**Poisson summation over `K`**): under the hypotheses above (without
  `m`), for Schwartz–Bruhat functions `g_v` on the `K_v`,

  `∑_{γ ∈ K} tensorCoeff S g γ F(ι γ) = κ ∑_{w ∈ K} tensorCoeff S (localFourier ψf μ · (g ·)) w 𝓕F(ι w)`.

### Theta series

- `exists_pos_le_normAtPlace`: if `N(y) ≠ 0`, all `normAtPlace w y` are at least some `m > 0`.
- `exists_decay_comp_mul`: if `‖G x‖ ≤ C (1 + ‖x‖)^{-r}` with `r ≥ 0` and `N(y) ≠ 0`, then
  `‖G (y z)‖ ≤ C₁ (1 + ‖z‖)^{-r}` for some `C₁`.
- `thetaSeries_tensorCoeff_eq`: under the hypotheses of `tsum_tensorCoeff_mul_eq`, for every `y`
  with `N(y) ≠ 0`,

  `θ(tensorCoeff S g, F)(y) = N(y)⁻¹ θ(tensorCoeff S (localFourier ψf μ · (g ·)), κ 𝓕F)(y⁻¹)`.

## Proofs

**Ideal lattices.** `ι` is injective and `ι(I) ⊆ ι(K)`, so a sum over `V` of a function supported
on `ι(I)` is the sum over `K` of its composition with `ι` (`Function.Injective.tsum_eq`,
`Function.Injective.summable_iff`).

**Coset tensors.** For `tensorCoeff_cosetIndicator_eq`: if `γ - γ₀ ∈ latticeIdeal m`, i.e.
`γ - γ₀ ∈ L_v(m_v)` for all `v`, then `γ - a_v = (γ - γ₀) + (γ₀ - a_v) ∈ L_v(m_v)` for `v ∈ S` and
`γ = (γ - γ₀) + γ₀ ∈ L_v(0)` outside `S` (where `m_v = 0`), so every factor is `1`. Otherwise some
`γ - γ₀ ∉ L_v(m_v)`; for `v ∈ S` the factor at `v` vanishes, and for `v ∉ S` the element `γ` is
not integral at `v`. `tensorCoeff_eq_sum` multiplies out `∏_{v ∈ S} Σ_i` by
`Fintype.prod_sum`.

**Characters on the dual lattice.** For `prod_character_eq_fourierChar`: for `v ∈ S`,
`(a_v - γ₀) w ∈ L_v(m_v) L_v(n_v - m_v) ⊆ L_v(n_v)`, on which `ψ_v` is trivial, so
`ψ_v(a_v w) = ψ_v(γ₀ w)`; for `v ∉ S`, `γ₀ w` is integral and `n_v = 0`, so `ψ_v(γ₀ w) = 1`. The
additive product formula for `x = γ₀ w` (whose exceptional set may be enlarged to `S ∪ S'`)
gives `∏_{v ∈ S} ψ_v(γ₀ w) = 𝐞(T(ι(γ₀ w)))⁻¹ = 𝐞(-T(ι γ₀ · ι w)) = 𝐞(B(ι γ₀, ι w))`.
`tensorCoeff_dualCoset_eq` follows by the same case distinction as for the coset tensors, now
with `latticeIdeal (n - m)` (the indicators `1_{L_v(n_v - m_v)}` for `v ∈ S` and integrality
outside `S`, where `n_v - m_v = 0`).

**Coset case.** By strong approximation (`exists_approx`) there is `γ₀ ∈ K` with
`γ₀ - a_v ∈ L_v(m_v)` for `v ∈ S` and `γ₀` integral outside `S`. Then the left side is
`∑_{γ} 1_{latticeIdeal m}(γ - γ₀) F(ι γ) = ∑_{l ∈ Λ_m} F(ι γ₀ + l)` (translation by `γ₀` and the
ideal-lattice lemmas), `Λ_m = idealLattice K (latticeIdeal m)`. Lattice Poisson summation
(`tsum_add_zlattice_eq`, whose hypothesis on the dual lattice follows from the decay of `𝓕F`)
gives `covol(Λ_m)⁻¹ ∑_{w ∈ Λ_m^*} 𝓕F(w) 𝐞(B(ι γ₀, w))`, and `Λ_m^* = Λ_{n-m}`
(`dualSubmodule_idealLattice`) turns this into a sum over `w ∈ latticeIdeal (n - m) ⊆ K`. By
`tensorCoeff_dualCoset_eq` the right side is `κ (∏_{v ∈ S} μ_v(L_v(m_v)))` times the same sum,
and the Tamagawa normalization `κ covol(Λ_m) ∏_{v ∈ S} μ_v(L_v(m_v)) = 1`
(`mixedGaussianConst_mul_covolume_mul_prod_latticeMass`) identifies the constants. The
summability statements are proved along the same chain of reindexings, from
`summable_add_zlattice_of_decay` and `summable_dualSubmodule_of_decay` of `LatticePoissonGeneral`.

**Local Fourier transforms.** `localFourier ψf μ v g y` is the integral `∫ ψ_v(x y) g(x) dμ_v`;
expanding `g`, the integral of the finite sum is the sum of the integrals (each integrable by
the first part of `padicLatticeFourier`), and each coset integral is
`μ_v(L_v(m)) ψ_v(a y) 1_{L_v(n_v - m)}(y)` by the second part of `padicLatticeFourier`.

**General tensors.** For each `v` the published `padicLatticeSchwartzExpansion` writes
`g_v = Σ_{i < N_v} c_{v,i} 1_{a_{v,i} + L_v(m_v)}`. With `m` equal to `m_v` on `S` and `0` elsewhere
and, for each choice `p` of indices, `a^p_v = a_{v, p_v}`, `tensorCoeff_eq_sum` writes
`tensorCoeff S g = Σ_p C_p tensorCoeff S (cosetIndicator · (a^p ·) (m ·))` with
`C_p = ∏_{v ∈ S} c_{v, p_v}`, and, with `localFourier_eq_sum`,
`tensorCoeff S (localFourier ψf μ · (g ·)) = Σ_p C_p tensorCoeff S (dualCosetCoeff ψf μ m a^p)`.
Since all the series are summable, the finite sum over `p` commutes with the sums over `K`
(`Summable.tsum_finsetSum`), and the coset case applies to each `p`.

**Theta series.** Put `F_y(z) = F(y z)`. By `fourierIntegral_comp_mul` (from
`MixedSpaceFourier`), `𝓕F_y(w) = N(y)⁻¹ 𝓕F(y⁻¹ w)`. Since `N(y) ≠ 0`, the coordinates of `y`
are bounded below by some `m > 0`, so `m ‖z‖ ≤ ‖y z‖` (`mul_norm_le_norm_mul` from
`ThetaDecay`) and `1 + ‖z‖ ≤ (1 + m⁻¹)(1 + ‖y z‖)`, which transfers the polynomial decay of `F`
to `F_y`; the same argument with `y⁻¹` (of norm `N(y)⁻¹ ≠ 0`, since `y y⁻¹ = 1`) applies to
`𝓕F_y`. Then `tsum_tensorCoeff_mul_eq` for `F_y` is the claimed identity after
`γ ↦ ι γ · y = y · ι γ` and `y⁻¹ · ι w = ι w · y⁻¹`.
