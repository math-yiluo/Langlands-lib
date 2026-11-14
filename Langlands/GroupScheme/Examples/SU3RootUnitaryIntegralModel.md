# The integral models `X_{r,s}` of the ramified quadratic unitary group

Module `Langlands.GroupScheme.Examples.SU3RootUnitaryIntegralModel`, namespace
`Langlands.GroupScheme.SU3Root`.

This module builds the integral models `X_{r,s}` of Kaletha–Prasad (KP) Appendix C.4 for the
unitary parameter group `U_{L/K}` of a ramified separable quadratic extension `L / K`. It
combines two earlier modules:

- `Langlands.GroupScheme.Examples.SU3RootUnitaryLattices`: the valuation arithmetic of KP §2.8,
  §3.2 and C.4 under the hypothesis `IsRamifiedQuadraticValuation K L ω` (`ω` is
  `σ`-invariant, `ω(K^×) ⊆ ℤ`, and some `π ∈ L` has `ω π = 1/2`). It provides `μ` (`mu K L ω`),
  a chosen `λ ∈ L^{tr=1,max}` (`traceOneMax`), the `K`-bases `latticeBasis r` of `L`, the
  generators `latticeCenter s` of the trace-zero line, and the charts `latticeData r s`.
- `Langlands.GroupScheme.Examples.SU3RootUnitaryIntegralChart`: the integral model
  `IntegralChart.model C` of `U_{L/K}` attached to a chart with integral cocycle coefficients,
  its integral points (`mem_integralPoints_iff`), and the model homomorphisms `chartHom`
  attached to integral changes of chart.

Notation. `σ = conjugation K L`. A rational point of `U_{L/K}` is a pair `(u, v)` in
`rationalParameters K L` with `v + σ(v) = u σ(u)`; the published `unitaryRationalPointsEquiv`
identifies the rational points of `unitaryParameterGroup K L` with these pairs. The published
subgroups of `Langlands.GroupScheme.Examples.SU3RootFiltration` are
`Parameters.filtration ω _ t = {(u, v) | ω(v) ≥ 2t}` and
`Parameters.centralFiltration ω _ t = {(0, v) | ω(v) ≥ t}`.

## Normality of the central filtration (namespace `Parameters`)

Here `L` is any field with a ring involution `c`, and the filtrations use a `c`-invariant
valuation `ω`.

- `conj_eq_of_first_eq_zero`: an element `(0, v)` is central: `g (0, v) g⁻¹ = (0, v)`.
- `centralFiltration_normal`: hence every central filtration subgroup is normal (an instance).
- `mem_filtration_sup_centralFiltration`: `p ∈ filtration r ⊔ centralFiltration s` if and only
  if `p = x z` with `x ∈ filtration r` and `z ∈ centralFiltration s`. This is the published
  `Subgroup.mem_sup_of_normal_right`.
- `filtration_sup_centralFiltration_min`: for real `r, s`,
  `filtration r ⊔ centralFiltration (min s (2r)) = filtration r ⊔ centralFiltration s`.
  If `s ≥ 2r`, every central filtration subgroup of depth at least `2r` is contained in
  `filtration r`, so both joins equal `filtration r`.

## Rings of integers

- `IsValuationIntegers O K ω` (a `Prop`) says that `O → K` has image exactly
  `{a ∈ K | ω(a) ≥ 0}`, where `ω` is evaluated on the image of `a` in `L`.
- `IsValuationIntegers.exists_eq` and `IsValuationIntegers.nonneg` are its two directions.

From now on `O` is a domain with fraction field `K`, `O`, `K`, `L` live in one universe,
`hω : IsRamifiedQuadraticValuation K L ω` and `hO : IsValuationIntegers O K ω`. The results
below are in the namespace `IsRamifiedQuadraticValuation`.

## The subgroup `X(K)_r · Z(K)_s`

KP define `X(K)_r = {(u, v) | (ω(v) − μ)/2 ≥ r}` and `Z(K)_s = {(0, v) | ω(v) − μ ≥ s}`
(C.4, via (3.2.3)).

- **`filtrationProduct r s`** is the subgroup
  `filtration ω (r + μ/2) ⊔ centralFiltration ω (s + μ)` of `rationalParameters K L`, that is
  `X(K)_r · Z(K)_s`, for arbitrary real `r` and `s`.
- `mem_filtrationProduct_iff`: `p` lies in it if and only if `p = x z` with
  `ω(x.second) ≥ 2r + μ`, `z.first = 0` and `ω(z.second) ≥ s + μ`.
- `filtrationProduct_min`: `filtrationProduct r (min s (2r)) = filtrationProduct r s`. This is
  the reduction of the central depth in KP Lemma C.4.1(3).

## The lattice charts and the models

- `omega_latticeData_coeff_nonneg_of_le`: if `s ≤ 2r`, every cocycle coefficient `cᵢⱼ` of
  `latticeData r s` has `ω(cᵢⱼ) ≥ 0`. Indeed `cᵢⱼ · latticeCenter s` is the correction
  `σ(λ) eᵢ σ(eⱼ) − λ σ(eᵢ) eⱼ` of two basis vectors of `Y_r`, which has value at least
  `2r + μ ≥ s + μ` (`le_omega_correction`). Unlike `omega_latticeData_coeff_nonneg`, this needs
  no condition `2r ∈ ℤ`.
- **`latticeChart hO r s : IntegralChart O K L (ULift (Fin 2))`** has chart
  `latticeData r (min s (2r))` (`latticeChart_data`): the `K`-basis `(ϖ^⌈r⌉, ϖ^⌈r − 1/2⌉ π)` of
  `L`, which is an `O`-basis of `Y_r = {u | ω(u) ≥ r}`; the element `λ = traceOneMax`; and the
  generator `latticeCenter (min s (2r))` of `Z_{min(s, 2r)} = {x | x + σ(x) = 0,
  ω(x) ≥ min(s, 2r) + μ}`. Its coefficients in `O` are chosen preimages of the chart
  coefficients, which exist by the previous item and `hO`.
- **`latticeModel hO r s : IntegralModel O K (unitaryParameterGroup K L)`** is
  `(latticeChart hO r s).model` (`latticeModel_eq`), for arbitrary real `r` and `s`. Its group
  scheme is `Spec O[a₀, a₁, b]` with the law
  `(a, b)(a', b') = (a + a', b + b' + ∑ᵢⱼ cᵢⱼ aᵢ a'ⱼ)`.
- `latticeModel_isSmooth`, `latticeModel_hasGeometricallyConnectedFibres`: the model is smooth
  and its structure morphism has geometrically connected fibres. `latticeModel_isAffineHom`:
  it is affine over `Spec O`.

## Integral points (KP Lemma C.4.2, Corollary C.4.3)

- `le_omega_sum_latticeBasis`: `∑ᵢ aᵢ eᵢ` has value at least `r` when the `aᵢ` come from `O`.
- **`exists_fieldPoint_iff`** (Lemma C.4.2 for `s ≤ 2r`): a rational point `p` is
  `fieldPoint (latticeData r s) a b` for some `a : ULift (Fin 2) → O` and `b : O` if and only if
  `p ∈ filtrationProduct r s`. Proof:
  - (⇒) Write `p = (u, b f + λ u σ(u))` with `u = ∑ aᵢ eᵢ`, so `ω(u) ≥ r`. Then `p = x z` with
    `x = (u, λ u σ(u))`, which has `ω(λ u σ(u)) ≥ 2r + μ` (`le_omega_traceOneMax_mul`), and
    `z = (0, b f)` with `ω(b f) ≥ s + μ` (`le_omega_mul_latticeCenter_iff`).
  - (⇐) Let `p = x z` as in `mem_filtrationProduct_iff` and `u = x.first`. By KP Lemma 3.2.2
    (`le_omega_of_le_omega_second`), `ω(u) ≥ r`, so the coordinates of `u` in `latticeBasis r`
    are integral (`le_omega_iff_latticeBasis`). The element
    `w = (x.second − λ u σ(u)) + z.second` has trace zero and value at least `s + μ`, because
    `s ≤ 2r`. So `w = c f` with `ω(c) ≥ 0` (`exists_mul_latticeCenter`,
    `le_omega_mul_latticeCenter_iff`), and `p` is the field point of these coordinates.
- **`mem_integralPoints_latticeModel_iff`**: a rational point `g` of `U_{L/K}` lies in the
  published subgroup `(latticeModel hO r s).integralPoints` if and only if
  `unitaryRationalPointsEquiv K L g ∈ filtrationProduct r s`. It combines the chart result
  `IntegralChart.mem_integralPoints_iff`, `exists_fieldPoint_iff` at depth
  `min s (2r) ≤ 2r`, and `filtrationProduct_min`.
- **`integralPoints_latticeModel_map`**: the image of the integral points of `X_{r,s}` under
  `unitaryRationalPointsEquiv K L` is exactly `filtrationProduct r s = X(K)_r · Z(K)_s`, for
  arbitrary real `r` and `s`.

## Transition homomorphisms

Let `r₁ ≤ r₂` and `s₁ ≤ s₂`, and write `sₖ' = min(sₖ, 2rₖ)`.

- `integralUniformizer hO ∈ O` is a preimage of the base uniformizer `ϖ`
  (`algebraMap_integralUniformizer`).
- `vecExponent r₁ r₂ i` is `⌈r₂⌉ − ⌈r₁⌉` for `i = 0` and `⌈r₂ − 1/2⌉ − ⌈r₁ − 1/2⌉` for `i = 1`
  (`vecExponent_zero`, `vecExponent_one`); `scalarExponent r₁ s₁ r₂ s₂` is
  `⌈s₂' + μ − ω(f₀)⌉ − ⌈s₁' + μ − ω(f₀)⌉`, where `f₀ = traceZeroElement K L`. Both are
  nonnegative (`vecExponent_nonneg`, `scalarExponent_nonneg`).
- `transitionMatrix hO r₁ r₂` is the diagonal matrix with entries `ϖ^{vecExponent r₁ r₂ i}`
  in `O`, and `transitionScalar hO r₁ s₁ r₂ s₂ = ϖ^{scalarExponent r₁ s₁ r₂ s₂}`.
  `algebraMap_pow_toNat` identifies their images in `K`.
- `latticeBasis_eq_mul` and `latticeCenter_eq_mul`: the basis vectors and the generators at
  the two depths differ by these powers of `ϖ`.
- `isChartChange_transition`: hence `(transitionMatrix, transitionScalar)` is an integral
  change of chart from `latticeChart hO r₂ s₂` to `latticeChart hO r₁ s₁`
  (`CoordinateData.IsChartChange`). Both charts use the same `λ`.
- **`latticeTransition hO hr hs : (latticeModel hO r₂ s₂).Hom (latticeModel hO r₁ s₁) (𝟙 _)`**
  is `IntegralChart.chartHom` of this change of chart: a homomorphism `X_{r₂,s₂} → X_{r₁,s₁}`
  of integral models over the identity of `U_{L/K}`.
- `latticeTransition_hom`: its group-scheme map is `BilinearCoordinate.linearHom` with this
  matrix and scalar.
- `vec_integralCoordinatesEquiv_latticeTransition`,
  `scalar_integralCoordinatesEquiv_latticeTransition`: on integral sections it acts on
  coordinates by `aᵢ ↦ ϖ^{vecExponent r₁ r₂ i} aᵢ` and `b ↦ ϖ^{scalarExponent r₁ s₁ r₂ s₂} b`.

## Relation to the literature

KP first normalize the depths (Lemma C.4.1) to `r ∈ J_{a/2a} = (1/2)ℤ`, `s ∈ J_{2a} = ℤ + 1/2`
and `s ≤ 2r + 1/2`. They then show that the coordinate change (C.4.1),
`(u, v) ↦ (u, v − u σ(u) λ)` with `λ ∈ L^{tr=1,max}`, identifies `X(K)_r · Z(K)_s` with
`Y_r × Z_s` (Lemma C.4.2). The model `X_{r,s}` is `Y_r × Z_s` with the transported law (C.4.2)
(Corollary C.4.3). KP's integral models `Y_r` and `Z_s` have `O`-points `Y_r` and `Z_s`.

This module uses a different route:

- **No normalization of `r`.** `Y_r` is the free `O`-module on `latticeBasis r` for every real
  `r`, and `filtrationProduct r s` is defined for every real `r`. So no rounding of `r` to
  `(1/2)ℤ` is needed.
- **Normalization of `s` by `min s (2r)`.** The chart uses `Z_{min(s, 2r)}`. Since the values
  of nonzero trace-zero elements lie in `ℤ + 1/2 + μ`, this lattice equals KP's `Z_{s'}` with
  `s' = inf{h ∈ J_{2a} | h ≥ min(2r, s)}` of Lemma C.4.1. That fact is not used in the Lean
  proofs. What is used is `filtrationProduct_min`, the part of Lemma C.4.1(3) that lowers the
  central depth to `min(s, 2r)`.
- **Integrality and Lemma C.4.2 without parity.** For depth `s ≤ 2r` the correction already
  has value at least `2r + μ ≥ s + μ`. So `omega_latticeData_coeff_nonneg_of_le` and
  `exists_fieldPoint_iff` do not use KP's parity step `ω(x) ≥ 2r + μ + 1/2`. They use KP
  Lemma 3.2.2, in the form `le_omega_of_le_omega_second`.
- **The model as a group scheme.** KP transport the law of `X` to the scheme `Y_r × Z_s`. Here
  `X_{r,s}` is the bilinear coordinate group scheme of the lattice chart. Its generic fibre is
  identified with `U_{L/K}` by `IntegralChart.model`, which uses the inverse of (C.4.1),
  `(a, b) ↦ (∑ aᵢ eᵢ, b f + λ u σ(u))`. "Schematic and connected" in Corollary C.4.3 is
  realized by `latticeModel_isSmooth`, `latticeModel_hasGeometricallyConnectedFibres` and
  `integralPoints_latticeModel_map`.
- **Transitions.** KP's morphism `X_{r₂,s₂} → X_{r₁,s₁}` in Lemma C.4.4 comes from the
  extension property of smooth models (their Corollary 2.10.10). Here `latticeTransition` is
  constructed directly, as an `IntegralModel.Hom` over the identity of `U_{L/K}`, given by an
  explicit diagonal change of coordinates. The kernel statement of Lemma C.4.4 is not part of
  this module.

The model depends on the chosen `λ = traceOneMax`, on the chosen bases and generators, and on
the chosen preimages in `O`. KP note (Corollary C.4.3) that the model is independent of `λ` up
to isomorphism; that independence is not formalized here.

In KP Appendix C.4, `K` is strictly Henselian with `ω(K^×) = ℤ`, so `L / K` is ramified. This
module assumes only the hypotheses `IsRamifiedQuadraticValuation K L ω` and
`IsValuationIntegers O K ω`. It does not use completeness, the Henselian property, or residue
fields.

## Sources

- KP, Appendix C.4, printed pp. 699–701 (PDF pp. 730–732): `X(K)_r`, `Z(K)_s`, Lemma C.4.1,
  (C.4.1), (C.4.2), `Y_r`, `Z_s`, Lemma C.4.2, Corollary C.4.3, and the statement of Lemma C.4.4.
- KP, §3.2(b), printed p. 149: Lemma 3.2.2.
