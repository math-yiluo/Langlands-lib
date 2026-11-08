# Mellin integrals of the class theta series of a Hecke character

Module `Langlands.Global.Hecke.HeckeClassMellin`, namespace `Langlands.Global.HeckeAssembly`.

Throughout, `K` is a number field, `V = mixedSpace K` its mixed space with norm `N`,
`C = fundamentalCone K`, `w = Units.torsionOrder K`, `χ` an actual Hecke character with
archimedean presentation data `dR, dC` (target hypotheses `IsRealCharacterPresentation`,
`IsComplexCharacterPresentation`), `ψ` a global additive character trivial on `K` with finite
components `ψf v`, self-dual Haar measures `μ v`, and archimedean scales `aR, aC`
(`IsRealAdditiveComponent`, `IsComplexAdditiveComponent`). Finite divisors are
`d : FinitePlaceDivisor K = FinitePlace K →₀ ℤ`; `principalDivisors K`, `principalGenerator`,
`principalUnitsEquiv`, `classRepresentative`, `classPrincipalEquiv`, `classPrincipalNegEquiv`
are from `Langlands.Global.Factors.HeckeDivisorClasses`; `thetaCoeff`, `classFactor`,
`fourierThetaCoeff`, `dualClassFactor`, `shellWeight`, `fourierShellWeight` and the divisor
Euler coefficients `DivisorEulerProduct.coefficient` are from the finite-side modules
`HeckeThetaCoefficients`, `HeckeFourierTheta`, `HeckeDivisorEulerProduct`,
`DivisorEulerProduct` (namespace `Langlands.Global`); `finiteMellin`,
`fourierFiniteMellin` are from `HeckeFiniteMellin`. The theta series
`thetaSeries a F y = ∑'_{γ ∈ K} a(γ) F(γ y)`, the dyadic-cone theta data `ThetaData` with its
meromorphic Mellin transform `M`, and the unfolding theorems are from
`Langlands.Global.Hecke.ThetaDecay`, `ConeMellin`, `ThetaUnfolding`; the Poisson summation
`thetaSeries_tensorCoeff_eq` from `AdelicPoisson`.

This module is the class-by-class part of the assembly of the Hecke global functional equation:
it builds the theta data of each divisor and evaluates their Mellin transforms in a right
half-plane as divisor Euler sums. It is an internal helper module for the proof of the published
statement `Langlands.Global.HeckeGlobalFunctionalEquationStatement`.

## Provenance

Internal helper for the proof of the published actual Hecke global functional equation
statement. The construction is Hecke's: a Hecke `L`-function is a finite sum over ideal classes
of Mellin transforms of theta series. In idelic form this corresponds to the decomposition of the
idele class group used in Tate's thesis (Cassels–Fröhlich 1967, §4.3 "Multiplicative Theory",
pp. 334 ff.). The particular objects (Gaussians adapted to `χ_∞`, Euler-test theta
coefficients, the dyadic-cone continuation) are internal choices of this formalization.

## Definitions

- `mixedChar dR dC = mixedCharFun ((dR ·).parity) ((dR ·).exponent) ((dC ·).weight)
  ((dC ·).exponent)` (an `abbrev`): the archimedean component `χ_∞` as a function on `V`.
- `gaussF aR aC dR dC = mixedGaussian aR aC ((dR ·).parity) ((dC ·).weight)`, the product
  Gaussian `F_{p,N}` adapted to `χ_∞` (scales `aR v`, `aC v`).
- `gaussG aR aC dR dC w = κ · 𝓕(gaussF)(w)`, with `κ = mixedGaussianConst aR aC` and
  `𝓕F(w) = ∫ 𝐞(T(x w)) F(x) dx` the Fourier transform for the trace pairing of the scales.

## Main results

- `classFactor_mul_integral_thetaSeries`: for a divisor `d`, `F` with Gaussian decay, `s` with
  `∑_D |c_s(D)| < ∞` (`c_s(D) = DivisorEulerProduct.coefficient ∅ (shellWeight χ · s) D`) and
  `F χ_∞ N^(s-1)` integrable,
  `classFactor χ d s · ∫_C (θ(a_d, F)(x) - a_d(0) F(0)) χ_∞(x) N(x)^(s-1) dx =
  w (∫_V F χ_∞ N^(s-1)) ∑'_{p ∈ principalDivisors K} c_s(p + d)`, `a_d = thetaCoeff χ d`.
- `tsum_eq_sum_classes`, `tsum_eq_sum_classes_neg`: for summable `f` on divisors,
  `∑' D, f D = ∑_{C ∈ Cl} ∑'_{p principal} f(p + rep C)` and `= ∑_C ∑'_p f(p - rep C)`.
- `gaussG_eq`: `gaussG = κ · c · mixedGaussian aR aC p (-N)`, `c = mixedGaussianFTConst`;
  `continuous_gaussF`, `continuous_gaussG`; `exists_gaussF_le`, `exists_gaussG_le`: Gaussian
  bounds `|F(z)| ≤ C e^{-c ‖z‖²}`.
- `exists_thetaData`: for every divisor `d` there are theta data `T` on the fundamental dyadic
  cone with `T.χ = mixedChar dR dC`, `T.l = mixedCharTwo …` (the doubling constant),
  `T.f x = θ(a_d, gaussF)(x) - a_d(0) gaussF(0)` and
  `T.g x = θ(b_d, gaussG)(x⁻¹) - b_d(0) gaussG(0)`, `b_d = fourierThetaCoeff χ ψf μ d`.
- `classFactor_mul_M_eq`: for such `T` and `s` with `1 < ‖T.ratio (s - 1)‖`, the summability
  above and integrability of `gaussF χ_∞ N^(s-1)`,
  `classFactor χ d s · T.M s = w Z(s) ∑'_p c_s(p + d)`, `Z(s) = ∫_V gaussF χ_∞ N^(s-1)`.
- `sum_classFactor_mul_M`: for theta data `T C` of the representatives `rep C` of all classes,
  `∑_C classFactor χ (rep C) s · (T C).M s = w Z(s) finiteMellin χ s`.
- `sum_classFactor_one_sub_mul_M`: given, for every class, the dual identity
  `classFactor χ (rep C) (1-s) ∫_C (θ(b, gaussG)(x⁻¹) - b(0) gaussG(0)) χ_∞(x) N(x)^(-s-1) dx =
  w Z_G ∑'_p c^S_s(-p - rep C)` (`c^S_s` the Fourier divisor coefficients with exceptional set `S`)
  and `‖T.ratio (1 - s)‖ < 1`,
  `∑_C classFactor χ (rep C) (1 - s) · (T C).M (1 - s) = w Z_G fourierFiniteMellin χ ψf μ S s`.

## Proofs

**Primal unfolding.** `integral_thetaSeries_unfold` (`ThetaUnfolding`) is applied with
`gen = principalGenerator`, `e = principalUnitsEquiv` (whose value at `(p, u)` is `u · gen p` by
definition), the support `mem_latticeIdeal_of_thetaCoeff_ne_zero`, the bound
`norm_thetaCoeff_le_one`, the unit equivariance `thetaCoeff_unit_mul` and the multiplicativity
of `mixedCharFun` (`MixedCharacter`). The coefficient identity `thetaCoeff_mul_eq_coefficient`
(with `principalDivisor (gen p) = p`) turns `a_d(gen p) χ_∞(gen p)⁻¹ N(gen p)^(-s) classFactor(s)`
into `c_s(p + d)`; it also gives the summability hypothesis of the unfolding, as
`|a_d(gen p)| |χ_∞(gen p)|⁻¹ N(gen p)^(-Re s) = |c_s(p + d)| / |classFactor(s)|` with
`classFactor(s) ≠ 0` and `p ↦ p + d` injective.

**Classes.** `classPrincipalEquiv : Cl × P ≃ Div` sends `(C, p)` to `p + rep C`; reindexing the
summable series along it and splitting the sum over the product (`Summable.tsum_prod'`, the class
group being finite) gives `tsum_eq_sum_classes`; similarly with `classPrincipalNegEquiv`.

**Theta data.** With `S = supp d ∪ {ramified places} ∪ supp n` (`n` the additive conductor
divisor, `additiveConductorDivisor`), the bridges `thetaCoeff_eq_tensorCoeff` and
`fourierThetaCoeff_eq_tensorCoeff` write `a_d` and `b_d` as tensor coefficients of the dilated
Euler tests and their local Fourier transforms; Poisson summation over `K`
(`thetaSeries_tensorCoeff_eq`, with the additive product formula
`additiveProductFormula_of_global`, polynomial decay of `gaussF` and of its Fourier transform
`c · mixedGaussian (-N)` from `exists_norm_mixedGaussian_le_rpow`) gives
`θ(a_d, gaussF)(x) = N(x)⁻¹ θ(b_d, gaussG)(x⁻¹)` on the cone. `coneThetaData` (`ThetaDecay`) then
produces `T` from: the supports (`mem_latticeIdeal_of_thetaCoeff_ne_zero`,
`exists_fourierThetaCoeff_support`), the bounds (`norm_thetaCoeff_le_one`,
`exists_norm_fourierThetaCoeff_le`), continuity and Gaussian bounds of `gaussF`, `gaussG`,
measurability and the cone bound of `mixedCharFun` (`exists_norm_mixedCharFun_le_cone`), and the
doubling relation `mixedCharFun_two_smul` with `mixedCharTwo_ne_zero`.

**Mellin identities.** `M_eq_integral` (`ConeMellin`) identifies `T.M s` with
`∫_C T.f χ N^(s-1)` when `1 < ‖T.ratio (s - 1)‖`; the integrand agrees on `C` with that of
`classFactor_mul_integral_thetaSeries`. The class sums follow by summing over the classes and
`tsum_eq_sum_classes` (`finiteMellin χ s` is by definition `∑' D, c_s(D)`). For the dual side,
`M_one_sub_eq_integral` identifies `T.M (1 - s)` with `∫_C T.g χ N^(-s-1)` when
`‖T.ratio (1 - s)‖ < 1`; reindexing `p ↦ -p` in `principalDivisors K` and
`tsum_eq_sum_classes_neg` give `fourierFiniteMellin χ ψf μ S s = ∑' D, c^S_s(D)`.
