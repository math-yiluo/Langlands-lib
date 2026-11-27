# Gårding smoothing on `G(𝔸)`: proof

`Langlands.Global.adelicGardingApproximation` proves
`Langlands.Global.AdelicGardingApproximationStatement` (module
`Langlands.Global.AdelicTemperedComponentInputs`): for a number field `F` and a group scheme `G`
over `F` as in the statement, there is one sequence `ψ_n` of bounded measurable compactly
supported functions on `G(𝔸)` such that, for every jointly continuous representation `ρ` of
`G(𝔸)` on a complex Banach space and every vector `u`, each `ρ(ψ_n) u = ∫ ψ_n(g) ρ(g) u dg`
(`dg = Measure.haar`) is a smooth vector of `ρ ∘ ofInfinite`, is fixed by `ρ(ofFinite l)` for `l`
in an open subgroup of `G(𝔸_f)`, and `ρ(ψ_n) u → u`.

## Source

L. Gårding, *Note on continuous representations of Lie groups*, Proc. Natl. Acad. Sci. USA 33
(1947), 331–332 (`garding-1947-continuous-representations`): averaging a vector against a smooth
compactly supported kernel gives a smooth vector (p. 331), and averages against nonnegative
smooth compactly supported kernels of integral one, with supports shrinking to the identity,
converge to the vector (the density argument on p. 332). The nonnegativity gives the norm
control in that argument; the Lean convergence lemma below records it as the two
normalizations `∫ ψ_n = 1` and `∫ |ψ_n| = 1`. On `G(𝔸) = G(F_∞) × G(𝔸_f)` the archimedean
factor is a Gårding kernel and the finite factor is the normalized indicator of a compact open
subgroup, the idempotent of that subgroup. The Lean proof follows this route.

## The construction

Everything except the last step is proved in namespace
`Langlands.Global.AdelicGardingApproximation` for an abstract topological group `A` with a
topological group isomorphism `s : A ≃ₜ* X × Y`, a Haar measure `μ` on `A` and monoid
homomorphisms `ιX`, `ιY` with `ιX x = s⁻¹(x, 1)` and `ιY y = s⁻¹(1, y)`. Here `X` is a real Lie
group (charted on a finite-dimensional normed space `𝔤`), `X` and `Y` are locally compact and
second countable, and the identity of `Y` has a neighbourhood basis of compact open subgroups.

For `b : X → ℂ`, `K ⊆ Y` and `k ∈ ℂ`, `kernel s b K k` is the function
`g ↦ k · b(x) · 1_K(y)` where `s g = (x, y)`.

- **Product decomposition of Haar measure.** `splitHaarFactor s μ μX μY` is the Haar scalar
  factor of the image measure `μ.map s` with respect to the product `μX.prod μY` of Haar measures
  of `X` and `Y`. `map_eq_splitHaarFactor_smul_prod` is the uniqueness of Haar measure on the
  second countable locally compact group `X × Y` (`Measure.isMulLeftInvariant_eq_smul`), and
  `splitHaarFactor_pos` shows the factor is positive since `μ ≠ 0`.
  `integral_eq_smul_integral_integral` combines this with Fubini's theorem: for continuous
  compactly supported `f`, `∫_A f dμ = c ∫_X ∫_Y f(s⁻¹(x, y)) dμY dμX` with `c` the factor.
  `integral_mul_split`, `integral_kernel` and `integral_norm_kernel` evaluate the integral of a
  product `f₁(x) f₂(y)`, of the kernel and of its absolute value.
- **Smoothness.** `integral_kernel_smul` uses the decomposition and `ρ(s⁻¹(x, y)) = ρ(ιX x) ρ(ιY y)`
  to write `∫ kernel(g) ρ(g) u dμ = c k ∫_X b(x) ρ(ιX x) w dμX` with
  `w = ∫_Y 1_K(y) ρ(ιY y) u dμY`, moving the bounded operator `ρ(ιX x)` through the inner
  integral. `integral_kernel_smul_mem_smoothVectors` then applies
  `Langlands.Archimedean.isSmoothVector_gardingIntegral` (module
  `Langlands.Representation.Archimedean.GardingDensity`) to the continuous representation
  `ρ ∘ ιX` of `X`, the smooth compactly supported kernel `b` and the vector `w`; smooth vectors
  form a complex subspace, so the scalar `c k` keeps the vector smooth.
- **Invariance.** For a subgroup `K` and `l ∈ K`, `kernel_mul_left` shows that the kernel is
  invariant under left translation by `s⁻¹(1, l)`, since `l y ∈ K ↔ y ∈ K`.
  `integral_kernel_smul_invariant` moves `ρ(ιY l)` inside the integral
  (`ContinuousLinearMap.integral_comp_comm`), so the integrand becomes the translate of the
  original one by `ιY l`, and left invariance of Haar measure (`integral_mul_left_eq_self`) gives
  `ρ(ιY l) ρ(kernel) u = ρ(kernel) u`.
- **Convergence.** `tendsto_integral_smul`: if continuous compactly supported `ψ_n` satisfy
  `∫ ψ_n = 1`, `∫ |ψ_n| = 1`, and for every identity neighbourhood `W` eventually
  `ψ_n(g) ≠ 0 → g ∈ W`, then `ρ(ψ_n) u - u = ∫ ψ_n(g) (ρ(g) u - u) dg` has norm at most `ε/2`
  once the support lies in `{g : ‖ρ(g) u - u‖ < ε/2}`, an identity neighbourhood by joint
  continuity of `ρ`. `eventually_kernel_ne_zero_mem` gives this support condition for kernels
  built on antitone neighbourhood bases `U_n` of `1 ∈ X` and `V_n` of `1 ∈ Y`, because
  `s⁻¹` is continuous at `(1, 1)`.
- **Assembly.** `exists_gardingKernels` chooses antitone countable neighbourhood bases `U_n`,
  `V_n` (first countability from second countability), compact open subgroups `K_n ⊆ V_n`, and
  by `Langlands.Archimedean.exists_normalizedSmoothWeight` smooth compactly supported weights
  `b_n` with `tsupport b_n ⊆ U_n`, `∫ b_n = 1` and `∫ |b_n| = 1`. With
  `k_n = (c · μY(K_n))⁻¹`, where `μY(K_n)` is positive and finite because `K_n` is open and
  compact, the kernels `ψ_n = kernel s b_n K_n k_n` are continuous (the indicator of the clopen
  `K_n` is continuous) and compactly supported, hence measurable and bounded, and satisfy
  `∫ ψ_n = ∫ |ψ_n| = 1`. The open subgroup in the statement is `K_n` itself.

The measurable structures on `X` and `Y` used for their Haar measures are the Borel
σ-algebras; the functions `ψ_n` and the integrals of the statement live on `A` with its given
Haar measure, so this choice does not enter the result.

## The adelic case

`adelicGardingApproximation` applies `exists_gardingKernels` with `A = AdelicGroupPoints F G`,
`s = AdelicGroupPoints.split F G`, `X = InfiniteAdelicGroupPoints F G` with the charted space
`InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth` and the Lie group structure
`InfiniteAdelicGroupPoints.smoothLieGroup F G hsmooth`, `Y = FiniteAdelicGroupPoints F G`,
`ιX = ofInfinite F G` and `ιY = ofFinite F G` (both equal to `(split F G).symm` of the pairs
`(x, 1)` and `(1, y)` by definition), and the compact open neighbourhood basis
`(finiteAdelicGroupCompactOpenBasis F G).2`. Local compactness and second countability of the
three groups are the instances of `Langlands.Global.AdelicGroupPointTopology` and
`Langlands.Global.AdelicGroupPolish`. The connected reductive hypothesis of the statement is not
used.
