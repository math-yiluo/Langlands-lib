# Reduction of the supercuspidal conductor lower bound to depth zero

## Setting

`K` is a `p`-adic field (`PadicField p`) with its canonical topology, valuation and local-field
structure, and `N = k + 2 ≥ 2`. For an irreducible supercuspidal class `π` of `GL_N(K)`,
`Henniart.Numerical.conductor K π ∈ WithTop ℕ` is its first fixed level, and
`IsNormalizedLevel K N π x` says that `x` is the normalized level of the class (Library module
`Langlands.BushnellKutzko.NormalizedLevel`).

## Declarations

- `exists_fixedVector_standard_of_unitSubgroup_one`: if a representation of `GL_{n+1}(K)` has a
  nonzero vector fixed by the first unit group `U¹` of a lattice chain `𝓛` in `K^{n+1}`, then it
  has a nonzero vector fixed by `U¹` of the standard chain `LatticeChain.standard hϖ`.
- `SupercuspidalConductorRankLowerBoundAtDepthZero` (proposition): the lower bound
  `N ≤ conductor K π` for the classes of normalized level `0`.
- `StandardDepthZeroShellNonzero` (proposition): for every `p`-adic field `K`, additive character
  `ψ` of conductor `𝔬_K` (`Conductor.HasIntegerConductor ψ`), σ-finite additive Haar measure `ν`,
  smooth representation `σ` of `GL_{n+1}(K)`, uniformizer `ϖ` and nonzero smooth vector `w` fixed by
  `U¹` of the standard chain `𝓢`, there is a smooth functional `ℓ` such that

  `∫_{ord(det g) = -(n+1)} Φ̂(g) f^ι(g) dg ≠ 0`,

  where `Φ = stratumTest K 𝓢 le_rfl ψ 0` is the indicator of `1 + ϖ M_{n+1}(𝔬_K)`,
  `Φ̂ = rectangularFourierIntegral ψ ν Φ`, `f = stratumCoefficient K σ ℓ w` is the coefficient
  `g ↦ ℓ(σ(g) w)`, `f^ι(g) = f(g^{-T})` (`GodementJacquet.coefficientIota`), and the measure is
  `RankinSelberg.generalLinearHaar K.Carrier n`. The module `Langlands.BushnellKutzko.DepthZeroShell`
  proves this proposition from finite matrix Gauss injectivity.
- `supercuspidalConductorRankLowerBoundAtDepthZero_of_nonzeroShell`:
  `StandardDepthZeroShellNonzero → SupercuspidalConductorRankLowerBoundAtDepthZero`.
- `supercuspidalConductorRankLowerBound_of_depthZero`:
  `SupercuspidalConductorRankLowerBoundAtDepthZero → SupercuspidalConductorRankLowerBoundStatement`.
- `supercuspidalConductorRankLowerBound_of_nonzeroShell`: the composite of the two implications.

## Provenance

The deduction follows Bushnell (1987), Theorem 3 and (5.1)(ii), (iv), printed pp. 198 and 208, at
positive level, and the depth-zero shell argument of Bushnell–Fröhlich (1985),
(3.3.10)–(3.3.15), printed pp. 259–260. Both sources are cited by the target statement
`SupercuspidalConductorRankLowerBoundStatement`.

## Proof

Every irreducible supercuspidal class has a normalized level `x`
(`normalizedLevelExistence`), and the lattice-chain formula for its level gives `0 ≤ x`. At
positive level, `exists_firstFixedLevel_eq_of_isNormalizedLevel` (the higher-rank Swan formula)
gives a finite first fixed level `a` with `(a − N)₊ = N x`. The right-hand side is strictly
positive, so `N ≤ a`.

At depth zero the lattice chain has a nonzero vector fixed by its first unit group.
An endomorphism that sends `L₀` into `L_e`, with `e` the period, sends `L_i` into
`L_(i+1)` for every `i`. For `0 ≤ i < e` this follows from monotonicity. The proof
reduces every other index to this range by scaling by a power of the uniformizer.
An integer basis of `L₀` extends to a field basis. The corresponding change of
basis conjugates the first unit group of the standard chain into the first unit
group of the given chain. Acting by the inverse change of basis gives a nonzero
fixed vector for the standard chain.

Take an additive character of conductor `𝔬_K` (a scale of the canonical character,
`RankinSelberg.UnramifiedUnitary.exists_scale_hasIntegerConductor`), its self-dual Haar measure,
and the functional-equation data `c, a` of the supercuspidal representation
(`GodementJacquet.Padic.exists_supercuspidalMatrixFunctionalEquationData`), with both Euler
polynomials `1`. The standard first-unit indicator is `stratumTest` with lattice depth one and
matrix parameter zero. The original zeta integral is constant in the spectral parameter
(`hasShiftedRationalValue_stratumTest`). The Fourier support bound
`toLin'_inv_smul_transpose_mem_of_fourier_ne_zero`, applied with `t = ϖ⁻¹` and filtration index
zero, shows that the reflected integrand is supported at determinant orders at least `−N`. The
shell identity for the monomial functional equation
(`setIntegral_ord_det_of_monomial_functionalEquation`) makes the integral zero at every order other
than `−a`. The hypothesis `StandardDepthZeroShellNonzero` supplies a smooth functional for which the
order-`−N` integral is nonzero, so `a = N`. The exponent comparison
`exists_exponent_eq_firstFixedLevel` gives a natural number `b` with `a = b` that is the first
fixed level of the class, so `conductor K π = b = N`; in particular `N ≤ conductor K π`. The theorem `supercuspidalConductorRankLowerBound_of_nonzeroShell`
combines this deduction with the positive-level case.
