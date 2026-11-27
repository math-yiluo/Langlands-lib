# Proof of the local Sobolev identity on `G(𝔸)`

In the module `Langlands.Global.AdelicSmoothVectorParametrixProof`, the theorem
`Langlands.Global.adelicSmoothVectorParametrix` proves
`Langlands.Global.AdelicSmoothVectorParametrixStatement`, defined in
`Langlands.Global.AdelicTemperedComponentInputs`.

## The statement

For a connected reductive group `G` over a number field `F`, smooth of relative dimension `d`, with
`G(F_∞)` carrying the atlas `InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth` modelled on
`smoothModel F d`, and for an open subgroup `L` of `G(𝔸_f)`: there are a finite set `S` of words in
`smoothModel F d` and bounded measurable compactly supported `φ_a : G(𝔸) → ℂ` such that every
`v ∈ E` that is a smooth vector of `ρ ∘ ofInfinite` and is fixed by `ρ(ofFinite l)` for `l ∈ L`
satisfies `v = ∑_{a ∈ S} ∫ φ_a(g) • ρ(g)(dρ(a) v) dg`, for every jointly continuous representation
`ρ` of `G(𝔸)` on a complex Banach space `E`. Here `dρ(a)` is `iteratedLieDerivative` for
`ρ ∘ ofInfinite` and `dg` is `Measure.haar` on `G(𝔸)`.

## Auxiliary results in this module

- `InfiniteAdelicGroupPoints.isClosedLinearRealization_matrixRealization_of_smooth` in `InfiniteAdelicLinearRealization`: for a closed
  matrix representation `ρ` of `G` (affine `G`), `matrixRealization F G ρ` is a closed linear
  realization of `G(F_∞)` for the atlas `smoothChartedSpace F G hsmooth`. The proof is that of
  `isClosedLinearRealization_matrixRealization` (which concerns the atlas `reductiveChartedSpace`)
  with this atlas's criterion `contMDiff_iff_coordinateSmooth`: closed embedding by
  `isClosedEmbedding_affineMatrix` and `archimedeanGLCoordinates`; smoothness by
  `GeneralLinear.coordinateSmooth_iff_contMDiff`; reflection of smoothness by
  `MatrixRepresentation.coordinateSmooth_of_postcomp` and `contMDiff_units_of_contDiff_val`.
- `InfiniteAdelicGroupPoints.exists_isClosedLinearRealization_of_smooth`: for connected reductive
  `G` such a realization exists, from `InfinitePlaceGroupPoints.exists_closedMatrixRealization`.
- `AdelicGroupPoints.ofInfinite_infinite_mul_ofFinite_finite`: `g = ofInfinite(g_∞) · ofFinite(g_f)`.
- `AdelicGroupPoints.infiniteSliceMeasure V`: the image under `infinite : G(𝔸) → G(F_∞)` of
  `Measure.haar` on `G(𝔸)` restricted to `finite⁻¹(V)`; `measurable_infinite`.
- `AdelicGroupPoints.isHaarMeasure_infiniteSliceMeasure`: for a compact open subgroup `V` of
  `G(𝔸_f)` it is a left Haar measure on `G(F_∞)`. Finite on compacts: `infinite⁻¹(K) ∩ finite⁻¹(V)`
  is the preimage of `K × V` under the homeomorphism `split`, hence compact. Left invariant:
  left translation by `ofInfinite(x)` preserves `finite⁻¹(V)` and `Measure.haar`, and
  `infinite(ofInfinite(x) g) = x · infinite(g)`. Positive on open sets: for `U` open and `u ∈ U`,
  `infinite⁻¹(U) ∩ finite⁻¹(V)` is open and contains `ofInfinite(u)`.
- `AdelicGroupPoints.integral_indicator_smul_eq`: for `V` open, `ρ` jointly continuous, `κ`
  continuous on `G(F_∞)` and `u` fixed by `ρ(ofFinite l)` for `l ∈ V`,
  `∫_{G(𝔸)} κ(g_∞) 1_{finite⁻¹V}(g) • ρ(g) u dg = ∫_{G(F_∞)} κ(x) • ρ(ofInfinite x) u d(infiniteSliceMeasure V)(x)`.
  On `finite⁻¹(V)`, `ρ(g) u = ρ(ofInfinite g_∞) ρ(ofFinite g_f) u = ρ(ofInfinite g_∞) u`, so the
  left side is the integral over `finite⁻¹(V)` of a function of `g_∞` (`integral_indicator`), which
  is the right side by `integral_map`.

## Proof of `adelicSmoothVectorParametrix`

Fix `F`, `G`, `hsmooth` and an open subgroup `L`. `G(F_∞)` is a Lie group for the atlas
(`InfiniteAdelicGroupPoints.smoothLieGroup`) with a closed linear realization `ρ_L`
(`exists_isClosedLinearRealization_of_smooth`).

1. Let `V = L ∩ K_f` with `K_f = FiniteAdelicGroupPoints.compactOpenSubgroup F G`. It is an open
   subgroup, closed (open subgroups are closed) inside the compact `K_f`, hence compact. So
   `μ_∞ = infiniteSliceMeasure V` is a left Haar measure on `G(F_∞)`.
2. `Archimedean.exists_sum_integral_iteratedLieDerivative` (module
   `LinearRealizationParametrix`) for `ρ_L` and `μ_∞` gives words `word j` (`j < M`) and continuous
   compactly supported `κ_j` on `G(F_∞)` with `w = ∑ⱼ ∫ κ_j(x) • π(x)(dπ(word j) w) dμ_∞(x)` for every
   strongly continuous `π` of `G(F_∞)` on a complex Banach space and every smooth vector `w`.
3. Put `φ'_j(g) = κ_j(g_∞) · 1_{finite⁻¹V}(g)`. The set `finite⁻¹(V)` is clopen, so `φ'_j` is
   continuous; its support lies in the compact `split⁻¹(tsupport κ_j × V)`. For `a` a word, let
   `φ_a = ∑_{j : word j = a} φ'_j` and `S = {word j : j < M}`. Each `φ_a` is continuous with compact
   support, hence measurable and bounded.
4. Given `ρ`, `v` as in the statement, apply step 2 to `π = ρ ∘ ofInfinite` (strongly continuous
   because `ρ` is jointly continuous) and `w = v`. Each `ρ(ofFinite l)` commutes with `π`
   (`factors_commute`), so by `OneParameterParametrix.iteratedLieDerivative_commute` it commutes
   with `dπ(word j)` on the smooth vector `v`; for `l ∈ V ⊆ L` the vectors `dπ(word j) v` are
   therefore fixed by `ρ(ofFinite l)`. By `integral_indicator_smul_eq` each integral over `G(F_∞)`
   against `μ_∞` is `∫_{G(𝔸)} φ'_j(g) • ρ(g)(dπ(word j) v) dg`.
5. Grouping the indices `j` by their word (`Finset.sum_fiberwise_of_maps_to`) and adding the
   integrals of the same word (`integral_finsetSum`; the integrands are continuous with compact
   support) gives `v = ∑_{a ∈ S} ∫ φ_a(g) • ρ(g)(dρ(a) v) dg`.

The Lie derivatives in the statement are the Library's `lieDerivative` (manifold derivatives at `1`
for the atlas `smoothChartedSpace`). They enter the proof through
`OneParameterParametrix.hasDerivAt_orbit_oneParameter`: along a smooth one-parameter subgroup `γ`
of `G(F_∞)`, the orbit `s ↦ π(γ s) w` has derivative `π(γ s)(lieDerivative π X w)` with
`X = mfderiv γ 0 1`, and the words consist of such tangent vectors `X` for the one-parameter
subgroups `s ↦ ρ_L⁻¹(exp(s bᵢ))`, `b` a basis of the Lie algebra of `ρ_L(G(F_∞))`.

## Modules used

- `Langlands.Representation.Archimedean.OneParameterParametrix`: the one-variable identity
  `δ = a'' + b` with continuous kernels and its iteration along one-parameter subgroups.
- `Langlands.Geometry.Manifold.LinearLieGroup.ContinuousHaarDensity`: continuous kernels in
  coordinates of the second kind as continuous compactly supported functions on the group.
- `Langlands.Representation.Archimedean.LinearRealizationParametrix`: the identity on a Lie group
  with a closed linear realization.
- Library modules: `InfiniteAdelicLinearRealization` (`matrixRealization`),
  `InfiniteAdelicGroupManifold` (`smoothChartedSpace`, `smoothLieGroup`,
  `contMDiff_iff_coordinateSmooth`), `AdelicGroupProduct` (`split`, `infinite`, `finite`,
  `ofInfinite`, `ofFinite`, `factors_commute`), `FiniteAdelicGroupCompactOpen`
  (`compactOpenSubgroup`), `AdelicGroupHaarMeasure` and `InfiniteAdelicModularCharacter`
  (measurable structures), and `HaarDensity` (`exists_haar_density_prodExp`).

## Literature

The route is that of J. Dixmier and P. Malliavin, *Factorisations de fonctions et de vecteurs
indéfiniment différentiables*, Bull. Sci. Math. (2) 102 (1978), §2 (Lemma 2.5, Remark 2.6, pp. 5–6)
and §3 (proof of Theorem 3.1, steps (1)–(3), pp. 6–7), pages of the English translation
*Factorizations of infinitely differentiable functions and smooth vectors* (paginated 1–24): a
one-variable identity along one-parameter subgroups, iterated over a basis of the Lie algebra, and
the Haar density in coordinates of the second kind. Here the one-variable identity is the
second-order `δ = a'' + b` of `OneParameterParametrix` instead of their identity of infinite order,
which suffices because the statement allows any finite set of words. The passage to `G(𝔸)` by the
indicator of a compact open subgroup of `G(𝔸_f)` is the usual one. Compare J. Bernstein, *On the
support of Plancherel measure*, J. Geom. Phys. 5 (1988), §3.4, Key Lemma, p. 686, a local Sobolev
bound for the values of smooth functions on a homogeneous space.
