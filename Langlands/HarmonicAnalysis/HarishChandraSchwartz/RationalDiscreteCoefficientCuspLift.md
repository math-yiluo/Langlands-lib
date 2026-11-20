# The direct cusp lift of discrete-series coefficients

Let `A` be a smooth representation of `G(F)` that is square integrable modulo
the image `A_G(F)` of a split component, with `A_G(F)` acting by a character
`χ`. Let `f` be a coefficient of `A`. This module writes down an explicit
cuspidal Schwartz function `φ` with central projection `p_χ(φ) = f`:

`φ = m⁻¹ · f · c`.

Here `c` is the indicator of a finite set of cosets in `G(F) ⧸ G¹` (one coset
over each point of the finite group `G(F) ⧸ G¹ A_G(F)`), and
`m = μ_A(A_G(F) ∩ G¹)` is the "central mass". The factor `c` is invariant
under `G¹`. So `φ` is bi-invariant under every compact subgroup `H` under
which `f` is bi-invariant, because such `H` lies in `G¹`. This gives the
level-preserving lifting of Waldspurger VIII.5 directly.

The main results are conditional. They take two published but unproved
propositions as hypotheses:

- `JointSpecialCompactBasisExistenceStatement` (module
  `Langlands.BruhatTits.SpecialCompact.JointBasisStatement`), which supplies
  the structural data of Corollary III.1.2;
- `RationalSchwartzConstantTermConvergenceStatement` (module
  `RationalCuspidalConvergenceStatements`): the radical integrals of all
  Schwartz functions converge.

From these the module proves the published target
`RationalCuspidalFixedCoefficientLiftingStatement` and the published
proposition `RationalCuspidalDiscreteCoefficientLowerInclusionStatement`.
Neither is proved outright here.

## Provenance

Waldspurger (2003), §VIII.4, printed p.330 (PDF p.96). For `χ` a character of
`A_G`, `p_χ f (g) = ∫_{A_G} χ⁻¹(a) f(a g) da`, the Library's
`centralProjection muA χ`. `E₂(G)_χ` is the set of discrete-series classes
whose central character restricts to `χ` on `A_G`, and `A₂(G)_χ` is the sum
of their coefficient spaces `A(ω)`. Theorem VIII.4.2 states
`p_χ(°C(G)) = A₂(G)_χ`, where `°C(G)` is the cuspidal Schwartz space.
§VIII.5, printed p.332 (PDF p.98), uses the `G × G`-invariance of `p_χ` to
deduce that the `H × H`-invariant coefficients of the classes in `E₂(G)^H_χ`
lie in `p_χ(°C_H)`. That is the published target
`RationalCuspidalFixedCoefficientLiftingStatement`.

Waldspurger proves the inclusion `A₂(G)_χ ⊂ p_χ(°C(G))` with wave packets.
By Theorem VII.2.5 the wave packet `f_ψ` of a smooth function `ψ` on the
orbit of `ω` is cuspidal, and Fourier inversion on `A_G` gives `p_χ f_ψ` as a
finite sum over the orbit. The present module takes a different, internal
route, which is not in Waldspurger:

- §III.7, printed p.273 (PDF p.39). For `ω` square integrable, `f ∈ A(ω)` and
  `ϕ ∈ C_c(G/G¹)`, the product `fϕ` lies in `C(G)`. In the Library this is
  `mul_mem_rationalSchwartz`, which needs the rapid decay of Corollary III.1.2
  (`hasRapidlyDecreasingCoefficientsOn_of_squareIntegrable`).
- The product with the transversal cutoff `c` is cuspidal. Coefficients of a
  representation that is square integrable modulo `A_G(F)` are cuspidal along
  every proper standard radical (module
  `RationalDiscreteCoefficientRadicalIntegrability`), and `c` is constant on
  each translate `x U y`, because the radical `U` lies in `G¹`.
- `p_χ(f c) = m f`. This is an elementary computation, given below.

There is no averaging over `H`, so the level is preserved automatically.

## A transversal cutoff

Section `Transversal`. `Γ` is a group with subgroups `N` and `A`. In the
application `N = G¹` and `A = A_G(F)`.

- `transversalCutoff N A : Γ ⧸ N → ℂ` (definition): the indicator of the set
  of classes `QuotientGroup.mk (Quotient.out m)` in `Γ ⧸ N`, for `m` running
  over `Γ ⧸ (N ⊔ A)`. So it is the indicator of one chosen `N`-coset inside
  each `N ⊔ A`-coset.
- `support_transversalCutoff_finite`: if `Γ ⧸ (N ⊔ A)` is finite, the support
  is finite.
- `hasCompactSupport_transversalCutoff`: if moreover `Γ` is a topological
  group and `N` is open, then `Γ ⧸ N` is discrete, so the cutoff has compact
  support.
- `exists_transversalCutoff_mul_eq_indicator`: for `N` normal and `A` central,
  and every `g`, there is `a₀ ∈ A` such that, as a function of `a ∈ A`,
  `c(a g)` is the indicator of `{a | a₀⁻¹ a ∈ N}`. The chosen representative
  of the coset of `g` has the form `g n b` with `n ∈ N` and `b ∈ A`, and one
  takes `a₀ = b`.
- `integral_transversalCutoff`: for `N` normal and open, `A` central, and a
  left-invariant measure `muA` on `A` (with `A` carrying an opens-measurable
  structure in which multiplication is measurable),
  `∫ c(a g) d muA(a) = muA.real (A ∩ N)` for every `g`. By the previous
  lemma the integrand is the indicator of a left translate of `A ∩ N`.
- `centralProjection_mul_transversalCutoff`: under the same hypotheses, if
  `f(a g) = χ(a) f(g)` for all `a ∈ A`, then
  `p_χ(f c) = muA.real (A ∩ N) · f`. The factor `χ(a)⁻¹ f(a g)` equals
  `f(g)`, so the integral is `f(g)` times the previous one.
- `centralProjection_smul_mul_transversalCutoff`: if moreover
  `m = muA.real (A ∩ N) ≠ 0`, then `p_χ(m⁻¹ · f c) = f`.
- `isBiInvariant_mul_quotient`: for `N` normal and `H ≤ N`, if `f` is
  `H`-bi-invariant then so is `g ↦ f(g) c(g N)`, for any function `c` on
  `Γ ⧸ N`. The coset of `h₁ g h₂` is that of `g`.
- `isIntegrableUnipotentCuspidal_mul_quotient`: for `N` normal, `U ≤ N` and a
  measure `muU` on `U`, if `f` is integrably cuspidal along `U`
  (`IsIntegrableUnipotentCuspidal muU f`), then so is `g ↦ f(g) c(g N)`. On
  each translate `x U y` the factor equals the constant `c(x y N)`
  (`quotient_mk_mul_mul_of_mem`).

## Coefficients with a central character

Section `Coefficients`.

- `coefficientFunctionSpace_mul_left`: if a subgroup `Z` acts on the smooth
  representation `A` by a character `χ`, then every `f` in the coefficient
  space `coefficientFunctionSpace A` satisfies `f(a g) = χ(a) f(g)` for
  `a ∈ Z`. The functions with this property form a submodule containing every
  coefficient `g ↦ ℓ(A(g) v)`.

## Rational points

Section `Rational`. The setting and local instances are those of
`RationalDiscreteCoefficientRadicalIntegrability`. `F` is a nonarchimedean
local field and `G` is connected reductive (`hG`), with a maximal split torus
`i` (`hi`) and a generic cocharacter `ν` (`hν`). `G¹` is
`rationalCommonNormKernel G`, which is open and normal. `A_G(F)` is the range
`(rationalPoints.map s).range` of a split component `s` (`hs`).

- `centralNormKernelMass_pos`: for every Haar measure `muA` on `A_G(F)`, the
  real measure of `A_G(F) ∩ G¹` (as the subgroup
  `(rationalCommonNormKernel G).comap (rationalPoints.map s).range.subtype`)
  is positive. The subgroup is open, since `G¹` is, and so it has positive
  Haar measure. It is compact by `isCompact_splitComponent_inf_commonNormKernel`,
  and so its measure is finite.

- `exists_cuspidal_lift`: the direct cusp lift. Its hypotheses are:
  - a compact subgroup `K0` (`hK0c`) with `SimultaneousStandardBasisAt i ν K0`
    (`hbasis`) and `FiniteCartanCovering F i ν K0` (`hcover`);
  - a compact open subgroup `K : OpenSubgroup (rationalPoints G)` (`hKc`) with
    `G(F) = P₀(F) K` (`hPK`), and a matrix representation
    `ρ : MatrixRepresentation G (Fin N)`, which together fix the Schwartz
    space `RationalSchwartzSpace hKc hPK ρ`;
  - a Haar measure `muA` on `A_G(F)`, the Borel structure on `G(F) ⧸ A_G(F)`
    and a Haar measure `mu` on that quotient;
  - a character `χ` of `A_G(F)` and `A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)`,
    square integrable modulo `A_G(F)` for `mu`, on which every `a ∈ A_G(F)`
    acts by the scalar `χ(a)`;
  - radical convergence for the given Schwartz space: for every proper `I`
    (`rootSet i ν I ≠ simpleRelativeRoots i ν`), every Haar measure `muU` on
    the radical `standardUnipotentPoints i ν (rootSet i ν I)`, every Schwartz
    function `φ` and all `x`, `y`, the function `v ↦ φ (x * v * y)` is
    `muU`-integrable.

  The conclusion: for every `f ∈ coefficientFunctionSpace A` there is `φ` in
  the Schwartz space such that
  - `φ ∈ rationalCuspidalSubmodule hKc hPK ρ`;
  - `centralProjection muA χ φ = f`;
  - for every compact subgroup `H` of `G(F)`, if `f` is `H`-bi-invariant then
    so is `φ`.

  The proof takes `φ = m⁻¹ · f · c`, with `c = transversalCutoff G¹ A_G(F)`
  and `m` the central mass. The quotient `G(F) ⧸ (G¹ ⊔ A_G(F))` is finite by
  `finite_rationalCentralQuotient` and
  `finiteIndex_splitValuationImage_of_isSplitComponent`, so `c` has compact
  support. Then `f c` is a Schwartz function by `mul_mem_rationalSchwartz`
  and Corollary III.1.2. It is cuspidal by
  `DiscreteCoefficientCutoff.coefficientFunctionSpace_le_integrableUnipotentCuspidalSubmodule`,
  `isIntegrableUnipotentCuspidal_mul_quotient` and
  `standardUnipotentPoints_le_rationalCommonNormKernel`. The projection is
  computed by `centralProjection_smul_mul_transversalCutoff`, with `m ≠ 0` by
  `centralNormKernelMass_pos`. Bi-invariance follows from
  `isBiInvariant_mul_quotient`, because a compact subgroup lies in `G¹`
  (`compactSubgroup_le_rationalCommonNormKernel`).

- `rationalCuspidalFixedCoefficientLifting_of_joint`: from
  `JointSpecialCompactBasisExistenceStatement.{u}` and
  `RationalSchwartzConstantTermConvergenceStatement.{u}`, it derives
  `RationalCuspidalFixedCoefficientLiftingStatement.{u, uV}`. The structural
  data `K0` come from `exists_constantTermPremises_of_joint`. For a class `ω`
  in `discreteSeriesCentralFixed`, the representative `ω.val.out.obj` is
  square integrable and `A_G(F)` acts on it by `χ`. The lift of
  `exists_cuspidal_lift` is cuspidal and `H`-bi-invariant, so it lies in
  `rationalCuspidalLevel hKc hPK ρ H`.

- `rationalCuspidalDiscreteCoefficientLowerInclusion_of_joint`: from the same
  two hypotheses, it derives
  `RationalCuspidalDiscreteCoefficientLowerInclusionStatement.{u, uV}`, the
  inclusion `A₂(G)_χ ⊆ p_χ(°C(G))` for the raw central-integral image. By
  `exists_cuspidal_lift` each coefficient space of a class in `E₂(G)_χ` lies
  in the image, and so `discreteSeriesCentralCoefficientSpace` lies in the
  span of the image (`discreteSeriesCentralCoefficientSpace_le_iff`). Central
  convergence on the whole Schwartz space is the published theorem
  `rationalSchwartzCentralConvergence`. So the span of the raw image is the
  raw image itself (`coe_schwartzCentralIntegralSpan_eq_image`).
