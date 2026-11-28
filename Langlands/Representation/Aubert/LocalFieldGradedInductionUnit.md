# Unit identities for the local-field GL induction product

The class `LocalFieldGraded.unit T` of the actual trivial line of
\(\mathrm{GL}_0(F)\) acts as the identity on both sides of
`Langlands.Aubert.LocalFieldGraded.multiplication T h`, for every
nonarchimedean local field realization `T` and every preservation witness
`h : LocalFieldBinaryProductExactLengthStatement`. This is the rank-zero unit
of Zelevinsky 1980 §1.7(c), printed p. 173. The two theorems are
`multiplication_unit_left` and `multiplication_unit_right`.

## Rank transport

`inclusion_eq_of_rank_equiv` compares classes in two summands whose ranks
are equal by `e : a = b`. If `A` is equivalent to the pullback of `B` along
`GeneralLinear.reindex (finCongr e)`, then `A` and `B` give the same element
of the graded group. After `subst`, the reindexing is the identity by
`GeneralLinear.reindex_finCongr_rfl`, and
`FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv` gives equality
of the exact classes.

## Unit laws

`leftUnit_object` evaluates the product of the unit with the class of an
actual finite-length `B` of rank `b`. By `multiplication_homogeneous` and
`binaryProduct_objects`, the product is the class of
`(binaryNormalizedProductFunctor T 0 b).obj (unitObject T, B)` in the
summand of rank `0 + b`. `binaryLeftZeroTensorEquiv` identifies this
representation with the action of \(\mathrm{GL}_{0+b}\) on
`unitObject T ⊗ B` through the rank cast and `B`.
`BinaryTensor.secondFactorUnitEquiv` removes the one-dimensional trivial
factor, and `BinaryTensor.compEquiv` carries this equivalence through the
pullback along the rank cast. `inclusion_eq_of_rank_equiv` with
`Nat.zero_add b` then gives the class of `B`. `rightUnit_object` is the same
argument with `binaryRightZeroTensorEquiv`,
`BinaryTensor.firstFactorUnitEquiv` and `Nat.add_zero a`.

Left multiplication by the unit and the identity are linear maps on the
graded group. `FiniteLengthGrothendieckGroup.hom_ext_object` says that a
linear map on an exact Grothendieck group is determined by its values on
classes of actual objects, and `DirectSum.linearMap_ext` says that a linear
map on the direct sum is determined by its compositions with the summand
inclusions. Together with `leftUnit_object` they give
`multiplication_unit_left`. The same argument applied to the flipped
bilinear map gives `multiplication_unit_right`.
