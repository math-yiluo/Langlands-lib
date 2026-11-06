# Relative parabolic quotients from two structural inputs

This internal construction specializes the published three-input reduction
using the published theorem
`Langlands.GroupScheme.RelativeParabolicQuotient.properAmbientCriterion_holds`.
The two remaining premises are exactly
`Langlands.GroupScheme.ParabolicDynamicStatement.{u}` and
`Langlands.GroupScheme.SelfNormalizingProperAmbientStatement.{u}`. This module
does not prove either premise or the unconditional quotient-existence target.

The declarations are in namespace
`Langlands.GroupScheme.RelativeParabolicQuotient`.

`properQuotientOfDynamicAndAmbient` takes these two structural statements and
the original data over any commutative ring `R : Type u`: actual group schemes
`G` and `P`, an inclusion `i : P ⟶ G`, reductivity of `G`, smoothness of `P`,
closedness of `i`, and parabolicity after every field algebra base change.
It returns an actual `ProperHomogeneousQuotient i`. It calls
`RelativeParabolicQuotientReduction.properQuotientOfDynamicAndAmbient` with
the two supplied statements and `properAmbientCriterion_holds`. Thus the
generic properness criterion is proved rather than retained as an input.

The imported reduction derives field self-normalization from the
parabolic-dynamic premise by supplying the published Borel conjugacy, Borel
self-normalization and dynamic connectedness proofs to rational descent.
It then supplies the published relative self-normalizer proof to the
original quotient assembly. The latter constructs the quotient and a
monomorphism to the proper ambient scheme, checks proper connected field
fibres, and invokes the generic properness criterion. The quotient and its
properness proof concern the same original subgroup and base.

`existenceStatement_of_dynamic_and_ambient` supplies the same published
properness proof to the reduction's extraction theorem. Its conclusion is
exactly the unchanged
`Langlands.GroupScheme.RelativeParabolicQuotient.ExistenceStatement.{u}`:
the quotient is proper, the projection is flat, surjective and quasi-compact,
and equality of images on every test scheme is equivalent to membership of
the right difference in the original subgroup functor.

Every universe `u`, every commutative ring, all field algebra structures and
all test schemes, including nonreduced ones, are retained. The two statement
premises remain explicit in both declarations. The provenance is composition
of published constructions and a published proof; no new literature assertion
or unconditional proof is claimed. The existing statement and its imports are
unchanged.
