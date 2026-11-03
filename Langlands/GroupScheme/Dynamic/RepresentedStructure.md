# Structural transport for represented dynamic subgroups

This internal construction works over `Spec R` for every commutative ring `R`
and every group scheme `G` whose underlying scheme is affine. For an arbitrary
cocharacter, `Dynamic.Affine.parabolicIso`, `centralizerIso`, and `unipotentIso`
identify any given representative of the corresponding dynamic subgroup functor
with the existing affine representative. Each `*_hom_comp` identity says the
isomorphism commutes with the inclusions into `G`.

The isomorphisms specialize the published
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy`. They use representation
on all test schemes, including nonaffine and nonreduced schemes; agreement only
on field-valued points would not supply their hypotheses.

The generic `SubgroupFunctor.IsRepresentedBy.isClosedSubgroup` transports
closedness between two representatives of one subgroup functor, over any base
scheme. The commuting identity factors the given inclusion as an isomorphism
followed by the known closed immersion. The three
`Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_*` results apply this to the
published closed inclusions from `Dynamic.AffineRepresentability`.

The supporting `IsClosedSubgroup.locallyOfFiniteType` proves that a closed
subgroup of a group scheme locally of finite type over its base is locally of
finite type over the same base. It factors the structure morphism through the
closed immersion and uses that closed immersions are locally of finite type
and that this property is stable under composition. This statement works over
an arbitrary scheme base. The already published
`IsClosedSubgroup.isAffineHom` supplies the analogous affine conclusion.

The provenance is a categorical derivation from the published represented
subgroup and affine dynamic-representability constructions and Mathlib's
morphism properties. No external structure theorem is assumed. There is no
field, smoothness, connectedness, reductivity, characteristic, splitness or
positive-rank hypothesis in the new dynamic results. These results do not
establish dynamic smoothness or natural Lie coordinates; those remain separate
dependencies of the structural determinant target.
