# Fourier theta coefficients of actual Hecke characters

Worker 1692 builds these internal coefficient identities for the dual side of
the global Hecke unfolding requested by Worker 1798 (package B4). They are the
Fourier counterparts of `HeckeThetaCoefficients` (package B3). Everything is
stated for an actual Hecke character `χ : HeckeCharacter K` of a number field
`K` in unrestricted universe `u`, its actual finite components
`χ.finiteComponent v`, the Library's actual local Euler tests `eulerTest`,
actual uniformizers `π_v = uniformizerUnit`, finite divisors
`FinitePlaceDivisor K`, and the supplied finite additive data: unitary additive
characters `ψf v` of the finite completions and self-dual Haar measures
`μ v : SelfDualHaar (topologicalData v) (ψf v)`. The local Fourier transform is
the Library's `HarmonicAnalysis.fourierTransform`, with the plus convention
`f̂(y) = ∫ ψ(x y) f(x) dμ(x)`. Where a theorem needs it, it also takes a finite
set `Sψ` outside which the additive conductors `n_v` of `ψf v` are zero. Only
the theorems in the last section take the real and complex presentations
`dR`, `hR`, `dC`, `hC` of the actual infinite components; there `χV` means
`Hecke.mixedCharFun` built from their parities, exponents and weights, exactly
as in `HeckeThetaCoefficients`. `q_v` is the actual residue cardinality and
`a_v` the multiplicative conductor of `χ_v`. The lattice of level `k` is
`additiveLattice k = π^(-k) O_v` (elements of order at least `-k`), and
`Hecke.latticeIdeal m` is the fractional ideal `∏ 𝔭_v^(-m(v))`.

## Local lemmas (namespace `Langlands.LocalFactor.PadicAbelian`)

- `dilateTest f a` is the test function `x ↦ f(x a)` for a unit `a`; it is
  locally constant and compactly supported because right multiplication by `a`
  is a homeomorphism (`dilateTest_apply` unfolds it).
- `fourierIntegral_comp_mul_unit`: for every function `f`, the Fourier integral
  of `x ↦ f(x a)` at `y` is `|a|⁻¹` times the Fourier integral of `f` at
  `y a⁻¹`, with the actual normalized absolute value. It is the existing scalar
  change of variables `integral_comp_mul_scalar` applied to
  `z ↦ ψ(z y a⁻¹) f(z)`. `fourierTransform_dilateTest` is the same statement
  for test functions, and `fourierTransform_dilateTest_uniformizer` specializes
  it to `a = π^k`: the transform of `x ↦ f(x π^k)` at `y` equals
  `q^k f̂(y π^(-k))`, since `|π^k| = q^(-k)`.
- `norm_fourierTransform_eulerTest_le`: `‖(eulerTest χ)^(y)‖ ≤ μ(O).toReal`,
  by bounding the integrand by the indicator of the integer ring (the Euler
  test has norm at most one and vanishes off the integers, by the B3 lemmas).
- `mem_additiveLattice_of_fourierTransform_eulerTest_ne_zero`: if the
  transformed Euler test is nonzero at `y`, then `y` lies in the lattice of
  level `n + a`, where `n` is the additive conductor of `ψ` and `a` the
  multiplicative conductor of `χ`. In the unramified case the Library formula
  `fourier_eulerTest_unramified` is a multiple of the indicator of level `n`;
  in the ramified case `fourier_eulerTest_ramified` is supported on the Gauss
  shell of order exactly `-(n + a)`.

## Global definitions (namespace `Langlands.Global.HeckeTheta`)

For `d : FinitePlaceDivisor K`, `μ' : K` and `s : ℂ`:

- `dilatedEulerTest χ d v` is the test function `x ↦ eulerTest_v(x π_v^(d v))`;
  `thetaCoeff_eq_finprod_dilatedEulerTest` records that the B3 theta
  coefficient is the unordered product of these at `γ`.
- `fourierEulerTest χ ψf μ v y` is the actual transform `(eulerTest_v)^(y)` for
  `ψf v` and `μ v`.
- `fourierThetaFactor χ ψf μ d μ' v := q_v^(d v) · fourierEulerTest_v(μ' π_v^(-d v))`;
- `fourierThetaCoeff χ ψf μ d μ' := ∏ᶠ v, fourierThetaFactor χ ψf μ d μ' v`;
- `dualClassFactor χ d s := ∏ v ∈ d.support, (q_v · χ_v(π_v)⁻¹ · spectralVariable_v(s))^(d v)`.

## Results

- (i) `fourierThetaFactor_eq_fourierTransform` and
  `fourierThetaCoeff_eq_finprod_fourierTransform`: each factor is exactly the
  actual Fourier transform of `dilatedEulerTest χ d v` at `μ'`, so the
  coefficient is the unordered product over finite places of these
  transforms. This is the uniformizer scaling lemma.
- `fourierEulerTest_eq_eulerTest`: when `a_v = 0` and `n_v = 0` the transformed
  Euler test is the Euler test itself (Library `fourier_eulerTest_eq_self`,
  using that the self-dual measure gives the integers mass one,
  `selfDualHaar_integerRing_eq_one`).
- `exists_finset_fourierThetaFactor_eq_eulerTest` (for every divisor `d`, a
  finite set outside which every factor, at every `μ'`, is the Euler test at
  `μ'` and `a_v = 0`), `exists_finset_fourierThetaFactor_eq_one`,
  `mulSupport_fourierThetaFactor_finite` and `fourierThetaCoeff_eq_prod` (the
  unordered product equals the finite product over any set outside which the
  factors are one). These take `Sψ` and its hypothesis.
- (ii) Support: `exists_fourierThetaCoeff_support` constructs the finite divisor
  `e` with `e(v) = n_v + a_v - d(v)` for every `v` and proves that a nonzero
  Fourier theta coefficient forces `μ' ∈ Hecke.latticeIdeal e`. Each nonzero
  local factor puts `μ' π_v^(-d v)` in level `n_v + a_v`, hence `μ'` in level
  `n_v + a_v - d(v)`. (This corrects the tentative `n - d - a` in the original
  request; the Library's ramified transform is supported in order
  `-(n + a)`.)
- Uniform bound: `exists_norm_fourierThetaCoeff_le` gives `C` with
  `‖fourierThetaCoeff χ ψf μ d μ'‖ ≤ C` for all `μ'`: on the finite set from
  `exists_finset_fourierThetaFactor_eq_eulerTest` each factor is bounded by
  `max (q_v^(d v) μ_v(O).toReal) 1`, elsewhere it is an Euler test of norm at
  most one.
- `fourierThetaFactor_unit_mul`: for a global integral unit `u`, each factor at
  `u μ'` is `χ_v(u)` times the factor at `μ'` (Library
  `fourier_eulerTest_mul_integralUnit`; `u` has local order zero).
- `fourierShellWeight_ord`: for a unit `x` of the completion, the actual
  Fourier shell weight `fourierShellWeight χ ψf μ v s` of order `ord x` equals
  `fourierEulerTest_v(x) · χ_v(x)⁻¹ · spectralVariable_v(s)^(ord x)`. It is
  `shellMellinTerm_ord_of_covariant` for the character `χ_v⁻¹`, whose
  covariance hypothesis is the Library unit covariance of the transform.
- `dualClassFactor_one_sub_mul_classFactor`:
  `dualClassFactor χ d (1 - s) · classFactor χ d s = 1` for every `s`, since
  `spectralVariable_v(1 - s) = q_v⁻¹ · spectralVariable_v(s)⁻¹`
  (`spectralVariable_one_sub`).

With the presentations `dR`, `hR`, `dC`, `hC` and the additive conductor set:

- (iii) `fourierThetaCoeff_unit_mul`: for `u : (𝓞 K)ˣ`,
  `fourierThetaCoeff χ ψf μ d (u μ') = (χV(ι u))⁻¹ · fourierThetaCoeff χ ψf μ d μ'`,
  where `ι = mixedEmbedding K`, by the local covariance and the finite product
  formula `finprod_finiteComponent_localUnit` from B3.
- (iv) `fourierThetaCoeff_mul_eq_coefficient`: for `μ' : Kˣ`, `s : ℂ` and any
  finite set `S` outside which `fourierShellWeight χ ψf μ v s 0 = 1`,
  `fourierThetaCoeff χ ψf μ d μ' · χV(ι μ') · N(ι μ')^(-s)` equals
  `DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s)
  (principalDivisor μ' - d) · dualClassFactor χ d s`. On a common finite set
  all four expressions become finite products. At each place, with
  `x_v = μ' π_v^(-d v)` of order `principalDivisor μ' v - d(v)`,
  `fourierShellWeight_ord` gives
  `fSW(ord x_v) = f̂_v(x_v) (χ_v(μ') χ_v(π_v)^(-d v))⁻¹ spectralVariable_v(s)^(ord x_v)`;
  multiplying by `(q_v χ_v(π_v)⁻¹ spectralVariable_v(s))^(d v)` gives
  `q_v^(d v) f̂_v(x_v) χ_v(μ')⁻¹ spectralVariable_v(s)^(principalDivisor μ' v)`,
  which is the local left-hand term (the B3 lemma `mixedNorm_cpow_eq_prod`
  supplies the norm power and `finprod_finiteComponent_localUnit` the mixed
  character). A private lemma `fourier_coefficient_algebra` carries out this
  scalar identity in `ℂ`.

These results do not establish Poisson summation, unit-cone integrals,
archimedean factors, analytic continuation or the global functional equation.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
