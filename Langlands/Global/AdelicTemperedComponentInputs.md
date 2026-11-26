# Summability of the logarithmic height and local smoothing on `G(𝔸)`

`Langlands.Global.AdelicTemperedComponentInputs` states three inputs for the construction of
irreducible unitary representations with tempered invariant distribution vectors in
`Langlands.Global.CyclicIrreducibleDistributionVectorStatement`.

## Sources

- J. Bernstein, *On the support of Plancherel measure*, J. Geom. Phys. 5 (1988), 663–710.
  `bernstein-1988-support-plancherel`, SHA-256
  `4d96d9b76127df990379dac18e578d613e1bed6c049ab8604f006a837925ea63`.
  Section 3.2 defines summable weights (pp. 681–682). Section 3.3 constructs the standard
  measure using reciprocal ball volumes and gives the integral criterion for summability
  (pp. 683–685). The Key Lemma of §3.4 bounds point evaluation by local Sobolev norms
  (statement p. 686 and proof p. 687).
- P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023), 109107.
  `delorme-2023-spectral-theorem-langlands`, folder SHA-256
  `e8b15973ea4ddbc7c7ba7f8fdf4eac5b42db2de9f74209baad19948cbfeb517b`.
  The locators refer to the published PDF `Delorme--On the spectral theorem of Langlands--2023.pdf`,
  SHA-256 `9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
  Section 2 defines the quotient height in (2.6)–(2.8) and gives
  `∫_[G] (1 + σ_[G](y))^(-d_G) Ξ_[G](y)² dy < ∞` in (2.10) (pp. 7–8).
  Remark 3.4 identifies `Ξ_[G]² dy` with the standard measure (pp. 11–12).
- J. Dixmier and P. Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment
  différentiables*, Bull. Sci. Math. (2) 102 (1978), no. 4, 307–330.
  `dixmier-malliavin-1978-factorisations`, retained English translation, SHA-256
  `b9ae377268ddfe90468dfcf21d08ee57df6a40496ba3c57276795a8ebbf5f07f`.
  Lemma 2.5 and Remark 2.6 give a localized one-variable identity (translation pp. 5–6).
  The proof of Theorem 3.1(1) uses product exponential coordinates (translation p. 6),
  and Theorem 3.3 applies the one-parameter method to smooth vectors (translation pp. 8–9).
- L. Gårding, *Note on Continuous Representations of Lie Groups*, Proc. Natl. Acad. Sci. USA
  33 (1947), no. 11, 331–332. `garding-1947-continuous-representations`, folder SHA-256
  `f2a043679079790908c82242ae25751de46192e32f150cc839fbb88f88e52777`.
  The theorem and proof occupy pp. 331–332 in `pnas01704-0031.png` (SHA-256
  `ffc4e9c60770f42af4591ef5dbf55550e3935acab7c1c3b36e62a7d1ff5786f6`) and
  `pnas01704-0032.png` (SHA-256 `ad64d279539e8af9aa01d109c1daadda7f68655596621a367ee19883407f1cc3`).
  Left Haar averaging differentiates through the translated kernel, and normalized smooth
  kernels with shrinking support approximate every vector. [PubMed Central](https://pmc.ncbi.nlm.nih.gov/articles/PMC1079067/?report=classic)

## Conventions

Each proposition quantifies over a number field `F : Type` and a connected reductive group scheme
`G` over `Spec F`, with `[IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]`.
Write `H = AdelicGroupPoints F G`, `Γ = rationalSubgroup F G`, `[G] = RationalQuotient F G`, and
`μ = Measure.haar` on `H`. The measure on `[G]` is
`μG = LeftCosetSpace.discreteQuotientMeasure Γ (isDiscrete_rationalSubgroup F G) μ`.

In the two local statements, `hsmooth : SmoothOfRelativeDimension d G.X.hom` fixes the charted
space `InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth` of `G(F_∞)` with model
`InfiniteAdelicGroupPoints.smoothModel F d`. A representation is a monoid homomorphism
`ρ : H →* (E →L[ℂ] E)` with jointly continuous action (`IsContinuousRepresentation ρ`), where
`E : Type` is a complex Banach space. Write `ρ∞ = ρ.comp (ofInfinite F G).toMonoidHom`.
A smooth vector of `ρ∞` has a smooth orbit map in this charted space, expressed by membership in
`Langlands.Archimedean.smoothVectors`. A test function is a bounded measurable complex function
on `H` with `HasCompactSupport`. Its action is the Bochner integral `ρ(φ) u = ∫ g, φ g • ρ g u ∂μ`.

## `RationalQuotientSummableLogHeightStatement`

Fix a maximal compact subgroup `K` of `H` and a matrix representation `rho` with
`IsClosedSubgroup rho`. Assume there is an affine minimal parabolic `P₀` with a closed immersion
`p₀ : P₀ ⟶ G` and `IsIwasawaCompact p₀ K`. There is a single `m : ℕ` such that for every compact
`C ⊆ H`, with `σ = rationalLogHeight F G rho`,

`∫⁻ y, #{q ∈ Γ : y.out⁻¹ * q * y.out ∈ C} · ENNReal.ofReal ((σ(y)^(2m))⁻¹) ∂μG < ∞`.

The count is `Set.encard` coerced to `ℝ≥0∞`. If `x` is replaced by `γ x` for `γ ∈ Γ`,
conjugating the counted elements by `γ` gives a bijection, so the count is a quotient function.

For the counting form of Bernstein's standard measure, fix a compact identity neighbourhood
`B ⊆ H`. Write `N_C(x)` for the count at a representative `x`. For a compact `A ⊆ H`, periodize
its indicator as `P_A(x,z) = ∑_{q ∈ Γ} 1_A(x⁻¹ q t)` with `t` representing `z ∈ [G]`. Unfolding gives
`∫_[G] P_A(x,z) dμG(z) = μ(A)`. At `z` in the image `[x B]` of `x B`, take `t = x b` with
`b ∈ B`. Every term counted in `N_C(x)` contributes to `P_(CB)(x,z)`, giving
`N_C(x) μG([x B]) ≤ μ(CB)`. In the other direction `P_B(x,z)` is supported in `[x B]`, and every
term there gives `x⁻¹ q x ∈ BB⁻¹`. This gives `μ(B) ≤ N_(BB⁻¹)(x) μG([x B])`.
Thus the count for `BB⁻¹` is comparable to `μG([x B])⁻¹`, and each compact `C` gives an upper
bound by the same density times a constant depending on `C` and `B`.

Delorme's density `Ξ_[G]²` is the reciprocal ball volume. The norm comparison for
`rationalLogHeight` is described in `AdelicWavePacketCompletenessReduction.md`. Since `σ ≥ 1`,
a large enough `2m` makes `σ^(-2m)` bounded by a constant times the decay factor in (2.10).
Together with the count estimate this gives the asserted finiteness for all compact `C`.
In Bernstein's criterion the summable weight is `σ^(2m)` and the integrand against the standard
measure uses its reciprocal.

For a test function `φ` with support `A`, the kernel of right convolution is the periodization
`∑_{q ∈ Γ} φ(x⁻¹ q t)`. If `q₀` contributes, each contributing `q` gives the element `q q₀⁻¹`
counted by `N_(AA⁻¹)(x)`. Cauchy–Schwarz bounds the squared kernel by
`‖φ‖∞² N_(AA⁻¹)(x) P_A(x,z)`. Unfolding in `z` and using the statement makes the kernel square
integrable for the range weight `σ^(-2m)`. This is the Hilbert–Schmidt input for right convolution
from `L²([G], μG)` to `L²([G], σ^(-2m) μG)`.

## `AdelicSmoothVectorParametrixStatement`

For each open subgroup `L ⊆ G(𝔸_f)` there are a finite set `S` of words in
`InfiniteAdelicGroupPoints.smoothModel F d` and test functions `φ a` for `a ∈ S`. These are chosen
for `L` and work for every jointly continuous representation `ρ` as above. For each smooth
vector `v` of `ρ∞` fixed by `ρ (ofFinite F G l)` for all `l ∈ L`, the identity is
`v = ∑ a ∈ S, ρ(φ a) (dρ∞(a) v)`, where `dρ∞(a)` is
`Langlands.Archimedean.iteratedLieDerivative` and `ρ(φ a)` uses `Measure.haar` on `H`.

The identity uses the local differentiation behind Bernstein's Key Lemma and the one-parameter
construction of Dixmier and Malliavin. In one variable, take a smooth cutoff `χ` on
`[0, ε]` with `χ(0) = 1` and `χ(ε) = 0`. The fundamental theorem of calculus for
`t ↦ χ(t) ρ∞(exp(tX)) w` gives the sum of the two integrals with kernels `-χ'` on `w` and `-χ`
on `dρ∞(X) w`, both kernels extended by zero outside the interval. Apply this construction
successively to the derivative vectors using a basis `X₁, …, X_r` at the identity. In the
coordinates `(t₁, …, t_r) ↦ exp(t₁ X₁) ⋯ exp(t_r X_r)`, changing from the coordinate measure
to the positive Haar density on a small compact box gives bounded measurable compactly
supported kernels on `G(F_∞)`. These coordinates and their Haar density are available using
`InfiniteAdelicGroupPoints.exists_isClosedLinearRealization` and
`IsExpLieAlgebra.exists_haar_density_prodExp` in the linear realization.

Choose a compact open subgroup `J ⊆ L` using `finiteAdelicGroupCompactOpenBasis`. The finite
factor of each kernel is the normalized indicator of `J`. The archimedean derivatives preserve
`J`-fixedness because the finite and infinite factors commute, so this average acts as the
identity on the derivatives. The product kernels are rescaled by the Haar normalization for
`AdelicGroupPoints.split`, which identifies `H` with `G(F_∞) × G(𝔸_f)`. The same identity can be
applied again to the smooth `L`-fixed derivative vectors.

## `AdelicGardingApproximationStatement`

There is one sequence `ψ : ℕ → H → ℂ` of test functions for all jointly continuous
representations `ρ` as above and all `u ∈ E`. For each `n`, the vector `ρ(ψ n) u` is smooth for
`ρ∞` and is fixed by `ρ (ofFinite F G l)` for all `l` in some open subgroup of `G(𝔸_f)`.
The sequence of these vectors tends to `u` in the norm topology of `E`.

Take the product of a nonnegative smooth bump of mass one on `G(F_∞)` and the normalized
indicator of a compact open subgroup of `G(𝔸_f)`, with the mass normalized for the adelic Haar
measure. Second countability and the compact open basis of `G(𝔸_f)` give a sequence of these
products whose supports eventually lie in every identity neighbourhood. Left translation by
the finite subgroup preserves its indicator, giving fixed vectors. The archimedean factor
smooths by Gårding's averaging argument, expressed by `Langlands.Archimedean.isSmoothVector_gardingIntegral`.
Continuity of the orbit map at `1` gives convergence by integrating the difference `ρ(g) u - u`
against these mass-one kernels.
