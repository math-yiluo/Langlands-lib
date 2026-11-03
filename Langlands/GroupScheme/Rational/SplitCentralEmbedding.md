# Actual central split tori inside maximal split tori

Author: Worker 1327.

This internal derivation uses the published factorization of central split
tori through maximal split tori. Over an arbitrary field and in an arbitrary
universe, every actual central split torus `a : A → G` factors through every
actual maximal split torus `i : T → G` of affine `G`. Writing the factor as a
morphism of commutative group schemes gives `f : A → T` with
`groupHom f ≫ i = a`. The factor is closed because its composite is closed and
`i` is closed. In particular, the construction applies to every supplied split
component; it does not select a substitute component.

`IsCentralSplitTorus.commFactor` chooses this actual morphism `f`, and
`commFactor_spec` proves its ambient-composite equation, closedness and
real-cocharacter injectivity. For a split component `ha`, it can be used
as `ha.isCentralSplitTorus.commFactor hi`.

The integral cocharacter map of a scheme monomorphism is injective by
cancelling its underlying scheme morphism after postcomposition. Tensoring
with the flat integer module `ℝ` preserves this injectivity. Thus the real
cocharacter map in the published `RealTorusSpace` is injective as well.
This argument does not need splitness, finite rank, or reductivity for the
injectivity assertions.

The provenance is internal. The geometric input is the already published
`IsCentralSplitTorus.exists_factor_of_isMaximalSplitTorus` in
`Rational.SplitTorusFactorization`, whose proof uses the split-torus image
theorem and maximality. This file specializes it to the identity closed
subgroup, uses `IsClosedSubgroup.of_comp`, and then applies flat scalar
extension. It asserts no identification with the common root annihilator,
no restriction-kernel equality, and no dimension formula.
