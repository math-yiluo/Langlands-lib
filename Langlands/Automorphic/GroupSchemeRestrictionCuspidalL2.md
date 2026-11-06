# Parabolic vanishing and `AdelicCuspidalForms` in `L²` of the restriction split-centre quotient

Author: Worker 112.

Getz--Hahn (`getz-hahn-2024-automorphic-representations`) define
`[G] = A_G G(F) \ G(A_F)` in (2.20)--(2.21), printed pp. 68--69. Their
Definition 6.5.1 and (6.18), printed p. 167, call an automorphic form
cuspidal when its integral over `[N]` vanishes for the unipotent radical `N`
of every proper parabolic and every `g`. Their (6.20)--(6.21), printed
p. 168, define `L²_cusp([G])` by the same vanishing almost everywhere.

The published modules `GroupSchemeParabolicQuotientL2` and
`GroupSchemeCuspidalFormL2` realize two continuous versions of this
condition as `L²` classes on the positive-torus quotient
`PositiveRationalQuotient F G T i`:
- continuous functions whose pullback lies in the published
  `parabolicCuspidalSubrepresentation`, i.e. it has convergent, everywhere
  vanishing constant terms for every proper rational parabolic;
- continuous functions whose pullback is the function of an element of the
  published `AdelicCuspidalForms`.

`AdelicCuspidalForms` is the published finite-smooth parabolic-vanishing
form space. Its Markdown states that it is not identified with the literal
GH form space, since GH (6.1) uses an algebraic tensor product. The Lean
names here contain `CuspidalForm` only to match those published names.

This module builds both constructions on the restriction quotient
`RestrictionSplitCentre.Quotient F G S j` of the published
`AdelicRestrictionSplitCentre`, which has the GH shape `A_G G(F) \ G(A_F)`.
It then compares them with the positive-torus versions through the
`L²` identification `quotientL2Equiv` of `GroupSchemeRestrictionQuotientL2`.

## Data

- `F : Type` is a number field.
- `G` is a group scheme over `Spec F` whose underlying scheme is affine and
  locally of finite type.
- `S` is a commutative group scheme over `ℚ` and `j` maps it into the Weil
  restriction `AffineWeil.groupScheme ℚ F G`.
- For parabolic vanishing: the explicit `hPD : ParabolicDynamicStatement`,
  `hG : IsConnectedReductive G`, and supplied measures `measuresU` on the
  published all-proper-parabolic radical quotients.
- For `AdelicCuspidalForms`: the same published parameters `Kinf`, `rho`,
  `hsmooth`, `hcalc`, `hPD`, `hG`, `hrho`, `hK` and `hN`.

## Continuous functions on the restriction quotient

- `continuousQuotientRightAction F G S j` is the complex representation of
  the adelic points on `C(Quotient F G S j, ℂ)` by `f ↦ f ∘ R(g)`, where
  `R(g)` is the published right translation `[x] ↦ [x * g]`. The identity
  and multiplication laws come from the published
  `LeftCosetSpace.rightTranslate_one` and `rightTranslate_mul`.
- `quotientContinuousPullback F G S j` sends `f` to `x ↦ f [x]` in the
  published `ContinuousRationalFunctions F G`. Invariance under rational
  points holds because they lie in the quotient subgroup
  (`principal_le_rationalSubgroup`).
- `quotientContinuousPullback_injective`: the pullback is injective,
  because the quotient map is surjective.
- `quotientContinuousPullback_rightAction`: the pullback intertwines
  `continuousQuotientRightAction` with the published `continuousRightAction`.
  It holds by definition.

## Parabolic vanishing

`quotientParabolicCuspidalSubrepresentation F G S j hPD hG measuresU` is the
preimage under the pullback of the published
`parabolicCuspidalSubrepresentation F G hPD hG measuresU`. The intertwining
law makes it a subrepresentation. Its membership lemma states that `f`
belongs exactly when its pullback does.

## Square-integrable continuous functions

Let `measureQ` be any measure on `Quotient F G S j`.
- `quotientContinuousL2Submodule F G measureQ` is the subspace of continuous
  `f` with `MemLp f 2 measureQ`.
- `quotientContinuousL2ToLp F G measureQ` sends such `f` to its class
  `MemLp.toLp`. `coeFn_quotientContinuousL2ToLp` states that the class
  agrees with `f` almost everywhere.
- `quotientContinuousL2ToLp_injective`: if `measureQ` is positive on
  nonempty open sets, two continuous functions with the same class are
  equal (Mathlib's `Measure.eq_of_ae_eq`).

Now also assume `hInv : QuotientRightInvariant F G measureQ` from
`GroupSchemeRestrictionQuotientL2`.
- `quotientContinuousL2Subrepresentation` is this subspace as a
  subrepresentation: composition with a measure-preserving map keeps
  `MemLp`. `quotientContinuousL2RightAction` is its representation.
- `quotientContinuousL2ToLp_rightAction` proves that passing to classes
  intertwines `quotientContinuousL2RightAction` with the
  `rationalQuotientL2RightAction F G measureQ hInv` of
  `GroupSchemeRestrictionQuotientL2`. It uses Mathlib's
  `Lp.toLp_compMeasurePreserving`.

## Continuous parabolic-vanishing `L²` functions

With `measureQ` and `hInv` as above:
- `quotientParabolicCuspidalL2Subrepresentation` is the intersection of
  `quotientParabolicCuspidalSubrepresentation` with the square-integrable
  subrepresentation. `QuotientParabolicCuspidalL2Functions` is its carrier
  and `quotientParabolicCuspidalL2RightAction` its representation.
  `mem_quotientParabolicCuspidalL2Subrepresentation` states membership as
  "pullback vanishes and `MemLp f 2 measureQ`".
- `quotientParabolicCuspidalL2ToContinuousL2` forgets the vanishing
  condition.
- `quotientParabolicCuspidalL2ToLp` is the intertwining map to
  `rationalQuotientL2RightAction`, given by `quotientContinuousL2ToLp` after
  forgetting. `coeFn_quotientParabolicCuspidalL2ToLp` gives its
  almost-everywhere formula, and `quotientParabolicCuspidalL2ToLp_injective`
  its injectivity for measures positive on nonempty open sets.
- `quotientContinuousParabolicCuspidalL2Image` is the range of this map, a
  subrepresentation of `rationalQuotientL2RightAction`.
  `mem_quotientContinuousParabolicCuspidalL2Image` states that membership
  means having such a continuous representative.

## `AdelicCuspidalForms` functions

The published `AdelicCuspidalForms` carry only an action of the finite
adelic points, so this part uses the finite factor.
- `continuousQuotientFiniteRightAction` restricts
  `continuousQuotientRightAction` along `AdelicGroupPoints.ofFinite`.
  `quotientFinitePullback` is the pullback as an intertwining map to the
  published `finiteRightAction`.
- `quotientCuspidalFormSubrepresentation` is the preimage under the pullback
  of the published `adelicCuspidalContinuousImage`, the range of the
  injective inclusion of `AdelicCuspidalForms` into continuous functions.
  By `mem_quotientCuspidalFormSubrepresentation`, `f` belongs exactly when
  some `phi` in `AdelicCuspidalForms` has continuous function equal to the
  pullback of `f`. So invariance under the quotient subgroup is imposed,
  not proved.

With `measureQ` and `hInv`:
- `quotientContinuousFiniteL2Subrepresentation` is the square-integrable
  subspace for the finite action.
- `quotientCuspidalFormL2Subrepresentation` is the intersection of the two.
  `QuotientCuspidalFormL2Functions` is its carrier and
  `quotientCuspidalFormL2FiniteRightAction` its representation;
  `mem_quotientCuspidalFormL2Subrepresentation` states membership.
- `quotientCuspidalFormL2ToContinuousL2` forgets the form condition.
- `rationalQuotientL2FiniteRightAction` restricts
  `rationalQuotientL2RightAction` to the finite factor.
- `quotientCuspidalFormL2ToLp` is the intertwining map to it, given by
  `quotientContinuousL2ToLp`. `coeFn_quotientCuspidalFormL2ToLp` and
  `quotientCuspidalFormL2ToLp_injective` give its almost-everywhere formula
  and injectivity for measures positive on nonempty open sets.
- `quotientCuspidalFormL2Image` is its range, with membership lemma
  `mem_quotientCuspidalFormL2Image`.
- `quotientCuspidalFormL2ToContinuousParabolic` sends each such function
  to itself in `QuotientParabolicCuspidalL2Functions` for the published
  mass-one radical measures `properParabolicQuotientMeasure`. Each element
  of `AdelicCuspidalForms` has pullback in the published
  `normalizedParabolicCuspidalSubrepresentation`, which is that space.
  `quotientCuspidalFormL2ToContinuousParabolic_toLp` proves that both maps
  give the same `L²` class.

## Comparison with the positive-torus quotient

Assume `h : subgroup F G S j = imageSubgroup F T G i`. Write
`ν⁺ = positiveRationalQuotientHaarMeasure F G T i` and
`ν = quotientHaarMeasure F G S j`.
- `continuousQuotientEquiv F G h` is the linear equivalence
  `C(PositiveRationalQuotient F G T i, ℂ) ≃ₗ[ℂ] C(Quotient F G S j, ℂ)`
  given by composition with the inverse of the published homeomorphism
  `quotientHomeomorph F G h`. Its two apply lemmas give the formulas.
- `quotientContinuousPullback_continuousQuotientEquiv`: the restriction
  quotient pullback of `continuousQuotientEquiv F G h f` equals the
  published `positiveQuotientContinuousPullback` of `f`. The homeomorphism
  is the identity on representatives (`quotientHomeomorph_mk`).
- `continuousQuotientEquiv_rightAction`: the equivalence intertwines the
  published `continuousPositiveQuotientRightAction` with
  `continuousQuotientRightAction`, by `quotientHomeomorph_rightTranslate`.
- `memLp_continuousQuotientEquiv_iff`: `continuousQuotientEquiv F G h f` is
  square integrable for `ν` exactly when `f` is for `ν⁺`. It uses the
  published `measurePreserving_quotientMeasurableEquiv`.
- `quotientContinuousL2ToLp_continuousQuotientEquiv`: the class of the
  transported function is `quotientL2Equiv F G h` of the published class
  `continuousL2ToLp`. It holds by definition.

The next results take arbitrary proofs `hInv` that `ν⁺` is right invariant
in the published sense and `hInv'` that `ν` is right invariant.
- `continuousQuotientEquiv_mem_parabolicCuspidalL2_iff`: the equivalence
  matches `quotientParabolicCuspidalL2Subrepresentation` with the published
  `positiveParabolicCuspidalL2Subrepresentation`.
- `parabolicCuspidalL2FunctionsEquiv` is the resulting linear equivalence of
  the carriers. `parabolicCuspidalL2FunctionsEquiv_rightAction` proves that
  it intertwines the right actions.
- `quotientParabolicCuspidalL2ToLp_parabolicCuspidalL2FunctionsEquiv`: on
  `L²` classes it is `quotientL2Equiv F G h`.
- `mem_quotientContinuousParabolicCuspidalL2Image_iff`: `φ` lies in
  `quotientContinuousParabolicCuspidalL2Image` for `ν` exactly when
  `(quotientL2Equiv F G h).symm φ` lies in the published
  `continuousParabolicCuspidalL2Image` for `ν⁺`.
- `continuousQuotientEquiv_mem_cuspidalFormL2_iff`,
  `cuspidalFormL2FunctionsEquiv`,
  `cuspidalFormL2FunctionsEquiv_finiteRightAction`,
  `quotientCuspidalFormL2ToLp_cuspidalFormL2FunctionsEquiv` and
  `mem_quotientCuspidalFormL2Image_iff` are the same statements for the
  published `positiveCuspidalFormL2Subrepresentation` and
  `cuspidalFormQuotientL2Image`, with the finite action.

## Split components

Assume that `characterRestrict i` is injective with finite-index range,
`hj : IsSplitComponent j`, `hs : IsSplitComponent i`, and that Haar measure
on `normOneSubgroup F G` is right invariant. These are the hypotheses of
`splitComponentL2RightAction` in `GroupSchemeRestrictionQuotientL2`, which
removes `h` by the published comparison theorem.
- `splitComponentParabolicCuspidalL2Image` is
  `quotientContinuousParabolicCuspidalL2Image` for `ν`, with the right
  invariance `quotientHaarMeasure_rightInvariant_of_splitComponents`, as a
  subrepresentation of `splitComponentL2RightAction`.
- `quotientParabolicCuspidalL2ToLp_injective_of_splitComponents` is
  injectivity for `ν`, from
  `quotientHaarMeasure_isOpenPosMeasure_of_splitComponents`.
- `mem_splitComponentParabolicCuspidalL2Image_iff` states that
  `splitComponentL2Equiv` matches it with the published
  `continuousParabolicCuspidalL2Image` for `ν⁺`, for any right-invariance
  proof of `ν⁺`.
- `splitComponentCuspidalFormL2Image`,
  `quotientCuspidalFormL2ToLp_injective_of_splitComponents` and
  `mem_splitComponentCuspidalFormL2Image_iff` are the same for
  `AdelicCuspidalForms`, with `rationalQuotientL2FiniteRightAction`.

## Provenance and scope

The quotient and the vanishing condition follow GH (2.20)--(2.21) and
Definition 6.5.1, (6.18). Every construction here is internal: preimages,
intersections and ranges of published objects, and transport along the
published identification of the two quotients.

The vanishing condition holds everywhere for continuous representatives,
with supplied or mass-one radical measures. The images are algebraic
ranges. They are not asserted to be closed, dense, or equal to GH's
almost-everywhere `L²_cusp([G])` of (6.20)--(6.21). Theorem 6.5.3 of GH
(density of cusp forms in `L²_cusp([G])`, printed p. 169) is not claimed.
Square integrability and invariance under the quotient subgroup are
imposed as conditions, not proved. The module does not identify
`AdelicCuspidalForms` with the literal GH cusp forms. It proves no strong
continuity, finite volume, existence of split components, or injectivity or
finite index of `characterRestrict i`.
