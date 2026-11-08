# Proof of the global functional equation of Hecke L-functions

Module `Langlands.Global.Factors.HeckeFunctionalEquationProof`.

**Theorem** `Langlands.Global.heckeGlobalFunctionalEquation_proof :
HeckeGlobalFunctionalEquationStatement.{u}` — it proves exactly the published statement
`Langlands.Global.HeckeGlobalFunctionalEquationStatement` of
`Langlands.Global.Factors.HeckeFunctionalEquationStatement`: for a number field `K`, an actual
Hecke character `χ` and a nontrivial unitary additive character `ψ` of the adeles trivial on `K`,
the local data exist, and for every choice of finite components `ψf`, self-dual measures `μ`,
archimedean scales `aR, aC` and presentations `dR, dC` of `χ_∞` and `dR', dC'` of `χ⁻¹_∞`, there
are `σ`, meromorphic `Λ, Λdual` and a finite set `S` of finite places with
`HasProd (finite L-factors of χ) (Λ s · infiniteDenominator s)` and
`HasProd (finite L-factors of χ⁻¹) (Λdual s · dualInfiniteDenominator s)` for `Re s > σ`,
`ε_v ≡ 1` for `v ∉ S`, and `Λ(s) = (∏_{v ∈ S} ε_v(s)) · infiniteEpsilon(s) · Λdual(1 - s)` for
`s` outside a discrete set (here: for every `s`).

## Proof

**Local data.** The first conjunct is `HeckeFunctionalEquation.localData χ ψ hdiag`
(module `HeckeLocalData`, from the adelic additive duality).

**Inputs.** After introducing the data and the `let`-bound functions of the statement, the proof
obtains:

- from `exists_archimedeanZeta` (`HeckeArchimedeanZeta`): entire nowhere-vanishing `E, E'` and
  `σ_A` with `Z(s) · infiniteDenominator(s) = E(s)` and `Ẑ(s) · dualInfiniteDenominator(s) =
  E'(s)` for `Re s > σ_A`, where `Z(s) = ∫_V gaussF χ_∞ N^(s-1)` and
  `Ẑ(s) = ∫_V F_{p,-N} χ⁻¹_∞ N^(s-1)` (the latter with the presentation `dR', dC'`), and the
  archimedean epsilon identity `κ c E'(1 - s) = infiniteEpsilon(s) E(s)` for all `s`
  (`κ = mixedGaussianConst`, `c = mixedGaussianFTConst`);
- from `exists_finiteMellin_common_halfPlane` (`HeckeFiniteMellin`): `σ_f` and a finite set `S`
  with `fourierShellWeight … 0 = 1` and `finiteEpsilon = 1` outside `S`, and for `Re s > σ_f`
  absolute summability of the divisor coefficients, `HasProd (L-factors of χ) (finiteMellin χ s)`,
  `HasProd (L-factors of χ⁻¹) (finiteMellin χ⁻¹ s)` and
  `fourierFiniteMellin χ ψf μ S s = (∏_{v ∈ S} ε_v(1 - s)) finiteMellin χ⁻¹ s`;
- for every ideal class `C`, theta data `T C` of the divisor `classRepresentative C`
  (`exists_thetaData`, `HeckeClassMellin`), all with the same doubling constant, hence the same
  ratio function; `exists_re_gt` (`ConeMellin`) gives `σ_M` with `1 < ‖ratio(s - 1)‖` and
  `‖ratio(1 - s)‖ < 1` for `Re s > σ_M`.

**Definitions.** With `w = Units.torsionOrder K`,

- `Λ(s) = (∑_C classFactor χ (rep C) s · (T C).M s) / (w E(s))`,
- `Λdual(s) = (∑_C classFactor χ (rep C) (1 - s) · (T C).M (1 - s)) /
  (w κ c E'(s) ∏_{v ∈ S} ε_v(1 - s))`,

and `σ = max(σ_A, σ_f, σ_M, σ_I)` with `σ_I = ∑ ‖(dR v).exponent‖ + ∑ ‖(dC v).exponent‖`, which
makes the archimedean zeta integrands integrable (`integrable_mixedGaussian_mul_mixedCharFun`).

**Meromorphy.** Each `(T C).M` is meromorphic on `ℂ` (`meromorphicOn_M`), `classFactor` and the
local epsilon factors are entire (`differentiable_classFactor`,
`finiteEpsilon_differentiable`), `E, E'` are entire; finite sums, products, composition with
`s ↦ 1 - s` (`MeromorphicAt.comp_analyticAt`) and quotients of meromorphic functions are
meromorphic.

**Euler products.** For `Re s > σ`: by `sum_classFactor_mul_M`,
`∑_C classFactor(s) M_C(s) = w Z(s) finiteMellin χ s`, so
`Λ(s) · infiniteDenominator(s) = finiteMellin χ s` using `Z(s) infiniteDenominator(s) = E(s) ≠ 0`.
On the dual side, the dual identity of each class
(`HeckeTheta.classFactor_one_sub_mul_integral_fourierTheta` of `HeckeDualThetaMellin`, the
Fourier counterpart of `classFactor_mul_integral_thetaSeries`, applied with `G = gaussG`, the
finite set `S`, a finite set outside which the additive conductors vanish
(`exists_finset_additiveConductor_eq_zero`) and the Gaussian bound `exists_gaussG_le`) and
`sum_classFactor_one_sub_mul_M` give
`∑_C classFactor(1 - s) M_C(1 - s) = w Z_G(s) fourierFiniteMellin χ ψf μ S s` with
`Z_G(s) = ∫_V gaussG χ⁻¹_∞ N^(s-1) = κ c Ẑ(s)` (`gaussG_eq`); hence
`Λdual(s) · dualInfiniteDenominator(s) = finiteMellin χ⁻¹ s`, using the finite epsilon
factorization and `Ẑ(s) dualInfiniteDenominator(s) = E'(s) ≠ 0`. The integrability of
`gaussG χ⁻¹_∞ N^(s-1)` needed there uses `χ⁻¹_∞(y) = χ_∞(y⁻¹)` (`mixedCharFun_dual_eq_inv_apply`)
and `mixedCharFun_inv`.

**Epsilon support.** `finiteEpsilon χ ψf μ v s = 1` for `v ∉ S` is part of the finite input;
the statement's `finiteEpsilon` is definitionally `HeckeFunctionalEquation.finiteEpsilon`.

**Functional equation.** Since `1 - (1 - s) = s`,
`Λdual(1 - s) = X(s) / (w κ c E'(1 - s) ∏_{v ∈ S} ε_v(s))` with
`X(s) = ∑_C classFactor(s) M_C(s)`, and the archimedean identity
`κ c E'(1 - s) = infiniteEpsilon(s) E(s)` gives
`(∏_S ε_v(s)) infiniteEpsilon(s) Λdual(1 - s) = X(s) / (w E(s)) = Λ(s)` for every `s` (all factors
are nonzero: `finiteEpsilon_ne_zero`, the archimedean epsilon factors are units, `E ≠ 0`). An
identity for every `s` holds in particular codiscretely (`Filter.Eventually.of_forall`).
