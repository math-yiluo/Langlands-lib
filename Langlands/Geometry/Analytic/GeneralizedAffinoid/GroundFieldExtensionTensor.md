# The ground field extension is the completed tensor product

This module proves that the presented ground field extension `A_L` of
`GroundFieldExtension` is boundedly isomorphic, as a `K`-algebra, to the
Library's projective completed tensor product
`CompletedTensorAlgebra.Algebra K A L`. The isomorphism is compatible with both
legs. All declarations live in the namespace
`Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension`.

`K` is an ultrametric normed field, `L` is a complete ultrametric normed field
with `NormedAlgebra K L`, and `A` is a `PresentedAffinoidAlgebra K`. Below,
`A ⊗̂_K L` denotes `CompletedTensorAlgebra.Algebra K A L`, with legs
`leftMap K A L : A → A ⊗̂_K L` and `rightMap K A L : L → A ⊗̂_K L`.

## From the tensor product to `A_L`

`fromTensor K L A` is the bounded `K`-algebra map `A ⊗̂_K L → A_L` given by the
Library's completed-tensor universal property `CompletedTensorAlgebra.lift`,
applied to `ι : A → A_L` and to the scalar map `L → A_L`.
`fromTensor_leftMap` and `fromTensor_rightMap` record its values on the two
legs.

## From `A_L` to the tensor product

Three norm bounds are needed first.

- `norm_leftMap_le_self` and `norm_rightMap_le_self`: both legs do not increase
  norms. They follow from the Library bounds `norm_leftMap_le` and
  `norm_rightMap_le`, from `‖1‖ = 1` in `L` and from `‖1‖ ≤ 1` in `A`
  (`norm_one_le`).
- `norm_one_tensor_le`: consequently `‖1‖ ≤ 1` in `A ⊗̂_K L`.

`tensorTuple K L A` is the tuple of first-leg images of the presentation
coordinates of `A`. `tensorTuple_monomial_le` bounds the norm of each
monomial in this tuple by the weight of the polyradius of `A`. It uses the
Library's `monomialValue_norm_le_weight`, the coordinate bound
`norm_coordinate_le` and the two bounds above.

`tensorEvaluation K L A` is the bounded `K`-algebra map from the weighted Tate
algebra over `L` to `A ⊗̂_K L` given by the Library's `evaluateCoefficientsHom`.
It sends coefficients through the second leg and the variables to
`tensorTuple`. Its values on constants and on variables are
`tensorEvaluation_constant` and `tensorEvaluation_X`.

- `tensorEvaluation_comp_coefficients`: its composite with coefficient
  extension from `K` to `L` is the presentation map of `A` followed by the
  first leg. Both sides are bounded `K`-algebra maps out of the weighted Tate
  algebra over `K` that agree on its variables.
- `tensorEvaluation_relations`: hence it kills every relation of `A_L`, since
  the presentation map of `A` kills `A.ideal`.
- `tensorEvaluation_ideal`: hence it kills the ideal of `A_L`. A bounded map
  kills the span of the relations because its kernel is an ideal, and it kills
  the closure of the span because it is continuous (`annihilates_closure`).

`toTensorRingHom` descends `tensorEvaluation` through the quotient by the
ideal of `A_L` (`Ideal.Quotient.lift`). `toTensor K L A` makes it a bounded
`K`-algebra map `A_L → A ⊗̂_K L`. Compatibility with `K`-scalars holds because
the evaluation sends constants through the second leg, which is a
`K`-algebra map. Boundedness, with constant `1`, follows from the
Library's quotient-norm bound `BoundedAlgHom.quotient_norm_bound` and the norm
bound `norm_evaluateCoefficients_le`. The descent is written with
`Ideal.Quotient.lift` rather than a bounded quotient lift over `K` because the
`K`-structure on `A_L` is the restriction of its `L`-structure, not the
quotient algebra structure over `K`.

- `toTensor_presentationMap`: `toTensor` sends the class of a series to its
  evaluation.
- `toTensor_iota`: `toTensor (ι a)` is the first-leg image of `a`. Write `a`
  as the class of a series over `K` and use
  `tensorEvaluation_comp_coefficients`.
- `toTensor_scalarMap`: `toTensor` sends `c · 1` to the second-leg image of `c`.

## The equivalence

- `toTensor_fromTensor`: the composite `A ⊗̂_K L → A_L → A ⊗̂_K L` is the
  identity. It agrees with the identity on both legs, by `fromTensor_leftMap`,
  `toTensor_iota`, `fromTensor_rightMap` and `toTensor_scalarMap`. The
  Library's uniqueness theorem `CompletedTensorAlgebra.hom_ext` then applies.
- `fromTensor_toTensor`: the composite `A_L → A ⊗̂_K L → A_L` is the identity.
  After precomposition with the presentation map of `A_L`, regarded over `K`,
  both sides agree on scalar constants from `L` and on the variables. The
  Library's uniqueness theorem `relative_hom_ext` for bounded maps out of a
  weighted Tate algebra over `L` then gives equality. The presentation map is
  surjective, so the composite is the identity.
- `tensorEquiv K L A : BoundedAlgEquiv K (A ⊗̂_K L) A_L` packages the two
  inverse bounded maps (`BoundedAlgEquiv.ofHomInv`). `tensorEquiv_apply` and
  `tensorEquiv_symm_apply` record its two directions.
- `tensorEquiv_leftMap`: the equivalence sends `leftMap a` to `ι a`.
- `tensorEquiv_rightMap`: it sends `rightMap c` to `algebraMap L A_L c`.

The equivalence asserts bounded inverse maps in both directions. It does not
assert that the quotient norm of `A_L` equals the projective tensor norm.

## Scope

`L` must be complete, because the Library's completed tensor product is only
universal for complete targets. Nothing else is assumed. Every degree and
transcendence degree of `L/K` is allowed, the valuations may be trivial, and
`K` need not be complete. `A` may be the zero algebra, nonreduced, or of arity
zero.

## Provenance

Berkovich (*Spectral theory and analytic geometry over non-Archimedean
fields*, AMS 1990, §2.3, printed p. 32) defines the ground field extension of
a `k`-affinoid algebra `𝒜` as the completed tensor product `𝒜 ⊗̂_k K` of §1.1,
printed p. 12. This module shows that the presented algebra `A_L` of
`GroundFieldExtension` is that completed tensor product up to a bounded
`K`-algebra isomorphism compatible with both legs. This justifies using `A_L`
as the ground field extension. The proof is internal: it combines the
Library's completed-tensor universal property, relative coefficient evaluation
of weighted Tate series, closed quotient descent, and the uniqueness theorems
for bounded maps out of completed tensor products and weighted Tate algebras.
