# Actual quotient parabolic jet coordinates after lifting to the group

Let `Q` be a supplied homogeneous quotient of an actual relative parabolic
`i:H→G` in a reductive group over `Spec R`. The actual representative of the
quotient parabolic family pulls back along any actual lift `g:T→G` to an
inclusion-compatible isomorphism with the conjugate of the original subgroup.
`quotientRepresentativeLiftIso` constructs this isomorphism from the all-test
quotient-family restriction law and uniqueness of actual subgroup
representatives. Its `hom_comp` theorem preserves the ambient inclusion.

The theorem `quotientRepresentativeLift_tensor_eq_zero_iff` identifies vanishing
of the evaluated-family tensor map with vanishing under the actual conjugate
tensor map on the same ambient tensor module. The actual jet section equivalence
induced by the representative isomorphism preserves the coordinate functions;
its injectivity proves the equivalence of vanishing conditions.

`quotientJet_tensor_eq_zero_iff_lift` applies when `g` followed by the quotient
projection is affine, flat and surjective. For an affine open `U` of the
quotient, it uses its actual inverse image `V` as an affine open of `T`.
Pulling coefficients along the actual `familyCoefficientHom`, vanishing in
the actual quotient family's jet over `U` is equivalent to vanishing in the
actual conjugate subgroup's jet over `V`. The proof combines actual family
tensor naturality, the representative isomorphism, and injectivity of the
actual jet-function pullback under affine faithfully flat base change.

This is an internal consequence of the imported actual parabolic quotient
family, subgroup representative uniqueness, actual jet coordinate naturality,
and faithful base-change APIs. It concerns the actual chosen quotient-family
representative and actual conjugated inclusion. Its affine faithfully-flat
hypotheses apply to the original quotient projection. The identification with
the classified Grassmannian point is a further obligation.
