# The Fourier transform of a function standard outside `S`

Module `Langlands.Global.RankinSelberg.FourierStandardOutsideProof`.

## 1. Content

This module proves the Library statement
`Langlands.Global.RankinSelbergGlobal.FourierStandardOutsideStatement.{u}`, declared in
[`EqualDualEulerFactorizationReduction`](EqualDualEulerFactorizationReduction.md) (Section
2.2 there). The theorem is `fourierStandardOutside`. The proof uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

The statement: let `F : Type u` be a number field,
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)` a unitary additive character, and
`S` a finite set of finite places with `FunctionalEquationComparison.FiniteAdditiveSupport ψ S`.
Then for every `n` and every `Φ : RowVector F n → ℂ`,

```text
IsStandardOutside F n S Φ → IsStandardOutside F n S (fourierTransform F n ψ.complex Φ).
```

* `FiniteAdditiveSupport ψ S`: at every finite place `v ∉ S` there is a character `ψ_v` of
  `F_v` with `IsCanonicalFiniteAdditiveComponent ψ v ψ_v`, that is
  `ψ_v(a) = ψ((0, single_v(a)))` for all `a ∈ F_v`, and with additive conductor `0`.
* `IsStandardOutside F n S Φ`: `Φ` vanishes off `integralOutside F n S`, the set of row
  vectors whose coordinates at every finite `v ∉ S` lie in `𝒪_v`. On that set, `Φ(x)` depends
  only on the archimedean parts `(x_j).1` and the local coordinates at the places of `S`.
* `fourierTransform F n ψ Φ x = ∫ Φ(y) ψ(∑_j y_j x_j) d(rectangleMeasure F 1 n)(y)`.

The statement assumes no integrability of `Φ`. Every step below holds for the Bochner
integral as defined, which is `0` for a non-integrable function.

**Provenance (internal).** The argument is ours. The fact it formalizes is classical: for a
local character of conductor `𝒪_v`, the Fourier transform of `1_(𝒪_v^n)` is a multiple of
`1_(𝒪_v^n)` (Tate's thesis, §2.2, Lemma 2.2.3, p.309, in Cassels–Fröhlich 1967, registered
as `tate-1967-thesis`; used by Cogdell 2004 on p.211 for `Φ̂ = ⊗_v Φ̂_v`). The proof here
works globally and does not factor `Φ`.

## 2. Local instances

The module declares five local instances. Two of them make the Library theorems
`GroupScheme.GeneralLinear.isAffine_groupScheme` and
`GroupScheme.GeneralLinear.smoothStatement` available to instance search for the group
scheme `GL_n` over `F`; the Library modules that use `rectangleMeasure` declare the same
instances. One states that the adelic points of the two-block unipotent subgroup are locally
compact, from `GeneralLinearBlockUnipotent.isClosed_adelicPoints`. Two put the Borel
measurable structure on rectangular adelic matrices, as `WhittakerIntegrals` does when it
defines `rectangleMeasure`. None of them adds a hypothesis.

## 3. Translation invariance of `rectangleMeasure`

`rectangleMeasure F k m` is the image of `normalizedBlockHaarMeasure`, a positive multiple
of Haar measure on the adelic points `H` of the two-block unipotent subgroup of `GL_(k+m)`,
under the coordinate map `H → M_(k×m)(𝔸)`.

* `rectangleCoordinateHomeomorph F k m`: the Library coordinate isomorphism
  `GeneralLinearBlockUnipotent.adelicCoordinates`, followed by `Multiplicative.toAdd`, as a
  homeomorphism `H ≃ₜ M_(k×m)(𝔸)`.
* `integral_rectangleMeasure_add_right`: for every `f` and every matrix `e`,
  `∫ f(y + e) d(rectangleMeasure F k m)(y) = ∫ f(y) d(rectangleMeasure F k m)(y)`.
  Proof: both integrals are integrals over `H`, by `MeasurableEmbedding.integral_map` for the
  homeomorphism. Let `a ∈ H` be the element with coordinates `e`. The coordinate map is a
  homomorphism to the additive group, so the coordinates of `a x` are those of `x` plus `e`.
  The measure on `H` is a scalar multiple of `Measure.haar`, so it is left invariant (after
  unfolding `normalizedBlockHaarMeasure` and `AdelicSubgroupPoints.normalizedHaarMeasure`).
  `integral_mul_left_eq_self` for `a` gives the equality.

## 4. The character

* `local_eq_one_of_conductor_eq_zero`: a character `ψ_v` of `F_v` with additive conductor
  `0` takes the value `1` on `𝒪_v`. This is `additiveConductor_spec`, with the additive
  lattice of index `0` identified with `𝒪_v` by `Hecke.mem_additiveLattice_zero_iff`.
* `local_exists_ne_one_of_conductor_eq_zero`: if `ψ_v` has conductor `0` and `u ∉ 𝒪_v`,
  there is `t ∈ 𝒪_v` with `ψ_v(t u) ≠ 1`. By `exists_nontrivial_at_conductor_succ` there
  is `z` of valuation at most `exp 1` (that is, `z ∈ ϖ_v⁻¹ 𝒪_v`) with `ψ_v(z) ≠ 1`. As
  `u ∉ 𝒪_v`, its valuation is at least `exp 1`. So `t = z / u` lies in `𝒪_v`, and `t u = z`.
* `character_eq_one_of_integralOutside`: if `FiniteAdditiveSupport ψ S` and the adele `b`
  has archimedean part `0`, component `0` at every place of `S` and integral components at
  every finite place outside `S`, then `ψ(b) = 1`. Write `b = (0, b_f)`. The Library theorem
  `HeckeFunctionalEquation.finite_additive_product` expresses `ψ((0, b_f))` as a finite
  product of the local values `ψ((0, single_v(b_v)))` over a finite set containing `S`. Each
  factor is `1`: at `v ∈ S` because `b_v = 0`, and at `v ∉ S` because the factor is
  `ψ_v(b_v)` with `b_v ∈ 𝒪_v` and `ψ_v` of conductor `0`.

## 5. Standard functions and translations

* `localCoordinates_add`: local coordinates are additive.
* `IsStandardOutside.add_eq`: if `Φ` is standard outside `S` and the row vector `e` has
  archimedean parts `0`, local coordinates `0` at the places of `S` and integral local
  coordinates outside `S`, then `Φ(y + e) = Φ(y)` for every `y`. If `y` is integral outside
  `S`, so is `y + e`, and the two vectors have the same archimedean and `S` coordinates. If
  `y` is not integral outside `S`, neither is `y + e`, and both values are `0`.
* `fourierTransform_eq_zero_of_add_eq`: if `Φ(y + e) = Φ(y)` for all `y` and
  `ψ(∑_j e_j x_j) ≠ 1`, then `Φ̂(x) = 0`. The substitution `y ↦ y + e`
  (`integral_rectangleMeasure_add_right`) gives `Φ̂(x) · ψ(∑_j e_j x_j) = Φ̂(x)`.

## 6. The proof of `fourierStandardOutside`

Let `Φ` be standard outside `S`. Both parts of `IsStandardOutside` are proved for `Φ̂`.

1. **Vanishing.** Let `x ∉ integralOutside F n S`. Then there are a finite `v ∉ S` and a
   coordinate `j` with `x_(v,j) ∉ 𝒪_v`. Let `ψ_v` be the canonical component at `v`, of
   conductor `0`, and choose `t ∈ 𝒪_v` with `ψ_v(t x_(v,j)) ≠ 1`
   (`local_exists_ne_one_of_conductor_eq_zero`). Let `δ = (0, single_v(t))` and let `e` be the
   row vector with `δ` in coordinate `j` and `0` elsewhere. Then `e` has archimedean parts `0`,
   local coordinates `0` at `S` (because `v ∉ S`), and integral local coordinates outside `S`
   (`t` at `v`, `0` elsewhere). So `Φ(y + e) = Φ(y)` by `IsStandardOutside.add_eq`. Moreover
   `∑_k e_k x_k = δ x_j = (0, single_v(t x_(v,j)))` (`RestrictedProduct.single_mul`), whose
   `ψ`-value is `ψ_v(t x_(v,j)) ≠ 1` by the definition of the canonical component.
   `fourierTransform_eq_zero_of_add_eq` gives `Φ̂(x) = 0`.
2. **Dependence on the archimedean and `S` coordinates.** Let `x`, `x'` be integral outside
   `S` with the same archimedean parts and the same local coordinates at `S`. The two
   integrands agree pointwise. If `y` is not integral outside `S`, both are `0` because
   `Φ(y) = 0`. Otherwise
   `ψ(∑_j y_j x_j) = ψ(∑_j y_j x'_j) · ψ(∑_j y_j (x_j − x'_j))`, and the last adele has
   archimedean part `0` (the archimedean parts of `x` and `x'` agree), component `0` at every
   place of `S`, and integral components outside `S` (products and differences of integral
   components). So its `ψ`-value is `1` by `character_eq_one_of_integralOutside`.

## 7. Relation to the Library

The statement `FourierStandardOutsideStatement` is a premise of the reduction
`equalDualEulerFactorizationReduction` of `EqualDualEulerFactorizationStatement` (module
`EqualDualEulerFactorizationReduction`). With this theorem that reduction no longer needs the
premise: `EqualDualEulerFactorizationStatement` follows from
`EqualEulerFactorizationStatement`, `SchwartzBruhatStatement` and
`ContragredientDualWhittakerStatement` alone. This module does not state that consequence.
