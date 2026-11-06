# Limit cones under induction on the actual Levi points

Author: Worker 1187. Module
`Langlands.Representation.Exponents.LeviInductionLimits`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

This is internal category infrastructure for the limit clause of
`LeviParabolicFunctorsPreserveLimitsStatement`. It transports an actual supplied
limit cone through the published normalized induction functor on Levi points.

The field `k : Type u` has the nonarchimedean local-field, valuation, topology
and Hausdorff instances. The ambient group scheme `G` is affine; its rational
points use `RationalPointFamily.pointTopology` and retain their local compactness
and nonarchimedean-group instances. The data are the actual parabolic
`p : P ⟶ G`, rational Levi `l : M ⟶ P` and matching geometric unipotent radical
`r : U ⟶ P`, including `IsIso (subgroupMultiplication l r)`. The topology on
`rationalPoints M` is the published `leviPointTopology l hl`.

`leviInductionFunctor_preservesLimits` proves
`PreservesLimitsOfSize.{v, v}` for the existing `leviInductionFunctor.{u, v}`.
The independently published
`isUnimodularModulus_pointImage_radical p r hp.isClosedSubgroup hr.1`
supplies the radical modulus input from these actual data. The published
`normalizedInductionFunctor_preservesLimits` then supplies limit preservation
for induction from the literal Levi image, at diagram size `{v, v}`. Pullback
along the inverse of `leviPointsEquiv p l hp hl` is an equivalence of smooth
representation categories, so it preserves these limits. Composing the two
functors gives the stated preservation for the published Levi-point induction.

`leviInductionLimitCone` takes a diagram `F` indexed by `J : Type v` with
`Category.{v} J` and a supplied `LimitCone F`. Its result has exactly the cone
obtained by applying `leviInductionFunctor` to the supplied cone; the preceding
preservation theorem and `isLimitOfPreserves` provide its universal property.
The source representation carriers stay in `Type v`, and induced carriers in
`Type (max u v)`. The construction asserts no existence of a source limit.

No quotient-compactness, unimodularity or root-presentation premise is added.
This unit establishes the limit clause only. The exact three-clause host target
still needs induction colimit preservation and Jacquet colimit preservation;
the separately owned quotient-compactness proof remains necessary for the
induction-colimit clause. No full host-target proof is submitted here.
