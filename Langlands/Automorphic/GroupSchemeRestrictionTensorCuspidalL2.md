# Tensor-smooth cusp forms in `L²` of the restriction split-centre quotient

Author: Worker 112.

Getz--Hahn (`getz-hahn-2024-automorphic-representations`) define
`[G] = A_G G(F) \ G(A_F)` in (2.20)--(2.21), printed pp. 68--69. Their
(6.1), printed p. 158, builds smooth functions from the algebraic tensor
product of smooth functions at the infinite places and smooth functions at
the finite places. Definition 6.5.1 and (6.18), printed p. 167, call an
automorphic form cuspidal when its constant term along every proper
parabolic vanishes.

The published module `GroupSchemeTensorCuspidalL2` keeps the literal tensor
condition of (6.1):
- `TensorAdelicCuspidalForms` is the space of tensor-smooth automorphic forms
  whose mass-one constant term vanishes for every proper rational parabolic.
  `tensorAdelicCuspidalToCuspidal` includes it into the published
  `AdelicCuspidalForms`, and `tensorAdelicCuspidalToContinuous` sends a form
  to its continuous function.
- On the positive-torus quotient `PositiveRationalQuotient F G T i`,
  `tensorPositiveQuotientSubrepresentation` imposes tensor smoothness
  (membership in the published `tensorSmoothSubrepresentation`) on the
  pullback, and `positiveTensorCuspidalFormL2Subrepresentation` intersects it
  with the published `positiveCuspidalFormL2Subrepresentation`.

This module builds the same construction on the restriction quotient
`RestrictionSplitCentre.Quotient F G S j` of the published
`AdelicRestrictionSplitCentre`, which has the GH shape `A_G G(F) \ G(A_F)`.
It starts from the `AdelicCuspidalForms` version in
`GroupSchemeRestrictionCuspidalL2` and compares the result with the
positive-torus version through `quotientL2Equiv` of
`GroupSchemeRestrictionQuotientL2`.

## Data

- `F : Type` is a number field.
- `G` is a group scheme over `Spec F` whose underlying scheme is affine and
  locally of finite type.
- `S` is a commutative group scheme over `ℚ` and `j` maps it into the Weil
  restriction `AffineWeil.groupScheme ℚ F G`.
- The published form parameters `Kinf`, `rho`, `hsmooth`, `hcalc`, `hPD`,
  `hG`, `hrho`, `hK` and `hN` of `TensorAdelicCuspidalForms`.

## Tensor smoothness on the restriction quotient

`quotientTensorSubrepresentation F G S j` is the preimage of the published
`tensorSmoothSubrepresentation F G` under `quotientContinuousPullback F G S j`
of `GroupSchemeRestrictionCuspidalL2`. It is a subrepresentation of
`continuousQuotientFiniteRightAction`, because the pullback intertwines the
right actions (`quotientContinuousPullback_rightAction`).
`mem_quotientTensorSubrepresentation` states that `f` belongs exactly when
its pullback is tensor smooth.

## Square-integrable tensor cusp-form functions

Let `measureQ` be a measure on `Quotient F G S j` and
`hInv : QuotientRightInvariant F G measureQ`.
- `quotientTensorCuspidalFormL2Subrepresentation` is the intersection of
  `quotientCuspidalFormL2Subrepresentation` with
  `quotientTensorSubrepresentation`. `QuotientTensorCuspidalFormL2Functions`
  is its carrier and `quotientTensorCuspidalFormL2FiniteRightAction` its
  representation of the finite adelic points.
- `mem_quotientTensorCuspidalFormL2Subrepresentation`: a continuous `f`
  belongs exactly when some `phi` in `TensorAdelicCuspidalForms` has
  continuous function equal to the pullback of `f`, and
  `MemLp f 2 measureQ`. Invariance under the quotient subgroup and square
  integrability are imposed, not proved.
- `quotientTensorCuspidalFormL2ToCuspidal` forgets tensor smoothness, an
  intertwining inclusion into `quotientCuspidalFormL2FiniteRightAction`.
- `quotientTensorCuspidalFormL2ToLp` is that inclusion followed by
  `quotientCuspidalFormL2ToLp`, an intertwining map to
  `rationalQuotientL2FiniteRightAction F G measureQ hInv`.
  `coeFn_quotientTensorCuspidalFormL2ToLp` states that the class agrees
  with the function almost everywhere.
- `quotientTensorCuspidalFormL2ToLp_injective`: the map is injective if
  `measureQ` is positive on nonempty open sets, by
  `quotientCuspidalFormL2ToLp_injective`.
- `quotientTensorCuspidalFormL2Image` is the range of the map, with
  membership lemma `mem_quotientTensorCuspidalFormL2Image`.
  `quotientTensorCuspidalFormL2Image_le` proves that it lies in
  `quotientCuspidalFormL2Image`.

## Comparison with the positive-torus quotient

Assume `h : subgroup F G S j = imageSubgroup F T G i`, and write
`ν⁺ = positiveRationalQuotientHaarMeasure F G T i` and
`ν = quotientHaarMeasure F G S j`. The results take arbitrary proofs `hInv`
that `ν⁺` is right invariant in the published sense and `hInv'` that `ν` is
right invariant.
- `continuousQuotientEquiv_mem_tensor_iff`: `continuousQuotientEquiv F G h f`
  lies in `quotientTensorSubrepresentation` exactly when `f` lies in the
  published `tensorPositiveQuotientSubrepresentation`. Both pullbacks are
  equal (`quotientContinuousPullback_continuousQuotientEquiv`).
- `continuousQuotientEquiv_mem_tensorCuspidalFormL2_iff` matches
  `quotientTensorCuspidalFormL2Subrepresentation` for `ν` with the published
  `positiveTensorCuspidalFormL2Subrepresentation` for `ν⁺`. It combines the
  previous item with `continuousQuotientEquiv_mem_cuspidalFormL2_iff`.
- `tensorCuspidalFormL2FunctionsEquiv` is the resulting linear equivalence
  `PositiveTensorCuspidalFormL2Functions ≃ₗ[ℂ]
  QuotientTensorCuspidalFormL2Functions`.
  `tensorCuspidalFormL2FunctionsEquiv_finiteRightAction` proves that it
  intertwines the finite right actions.
- `quotientTensorCuspidalFormL2ToLp_tensorCuspidalFormL2FunctionsEquiv`: on
  `L²` classes the equivalence is `quotientL2Equiv F G h` applied to the
  published `positiveTensorCuspidalFormL2ToLp`.
- `mem_quotientTensorCuspidalFormL2Image_iff`: `φ` lies in
  `quotientTensorCuspidalFormL2Image` for `ν` exactly when
  `(quotientL2Equiv F G h).symm φ` lies in the published
  `tensorCuspidalFormQuotientL2Image` for `ν⁺`.

## Split components

Assume that `characterRestrict i` is injective with finite-index range,
`hj : IsSplitComponent j`, `hs : IsSplitComponent i`, and that Haar measure
on `normOneSubgroup F G` is right invariant. These are the hypotheses of
`splitComponentL2RightAction` in `GroupSchemeRestrictionQuotientL2`, which
removes `h` by the published comparison theorem.
- `splitComponentTensorCuspidalFormL2Image` is
  `quotientTensorCuspidalFormL2Image` for `ν`, with the right invariance
  `quotientHaarMeasure_rightInvariant_of_splitComponents`.
- `quotientTensorCuspidalFormL2ToLp_injective_of_splitComponents` is
  injectivity for `ν`, from
  `quotientHaarMeasure_isOpenPosMeasure_of_splitComponents`.
- `mem_splitComponentTensorCuspidalFormL2Image_iff` states that
  `splitComponentL2Equiv` matches it with the published
  `tensorCuspidalFormQuotientL2Image` for `ν⁺`, for any right-invariance
  proof of `ν⁺`.

## Provenance and scope

The quotient, the tensor condition and the vanishing condition follow GH
(2.20)--(2.21), (6.1), Definition 6.5.1 and (6.18). Every construction here
is internal: preimages, intersections and ranges of published objects, and
transport along the published identification of the two quotients.

The images are algebraic ranges. They are not asserted to be closed, dense,
or equal to GH's `L²_cusp([G])` of (6.20)--(6.21), printed p. 168. Theorem
6.5.3 of GH (density of cusp forms in `L²_cusp([G])`, printed p. 169) is
not claimed. The tensor space is not identified with
`AdelicCuspidalForms`; only the inclusion is proved. Square integrability
and invariance under the quotient subgroup are imposed as conditions, not
proved. The module proves no finite volume, existence of split components,
or injectivity or finite index of `characterRestrict i`.
