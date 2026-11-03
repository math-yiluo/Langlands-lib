# Actual parabolic subgroup functors and identity-test comparisons

Author: Worker 1291.

This internal interface reuses `IsParabolicFunctor` from
`Rational.MinimalParabolic`. That predicate means that the functor is the range
on every test scheme of an actual closed parabolic embedding over the ground
field, satisfying the existing `IsParabolicSubgroup`. It is not a predicate
on an abstract subgroup of rational points.

`ParabolicFunctor G` is the subtype of those functors, with the inherited
all-test inclusion order. `ParabolicFunctorBelow P` imposes inclusion in a
specified subgroup functor `P`.

`isParabolicFunctor_iff_of_isRepresentedBy` proves that for any closed
representative `j : H → G` of `F`, the existential predicate holds exactly
when `IsParabolicSubgroup j` holds. The forward implication uses the published
`IsParabolicSubgroup.of_range_eq`; the reverse implication uses `j` itself as
the representative. `isParabolicFunctor_range_iff` specializes this to a closed
embedding's range. Thus the predicate does not depend on the choice of a
closed representative.

`SubgroupFunctor.rationalPointSubgroup F` is exactly
`F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))`, viewed in the existing
`RationalPoint k G.X` type. Intersections, images, and inverse images retain
their defining membership conditions under this evaluation. In particular,
mapping the inverse image back into `G(k)` is intersection with the range
of the embedding, with no surjectivity claim about unrelated rational-point
quotients.

`IsRepresentedBy.rationalPointsEquiv` is the existing
`IsRepresentedBy.pointsEquiv` evaluated at that same identity test scheme.
It identifies the rational points of any representative with the subgroup
in the ambient group, and the displayed coercion and inverse equations give
the actual embedding. It constructs no topology or continuity assertion;
the represented-subgroup point-topology development remains the relevant
separate interface.

Every declaration is universe-polymorphic in `u`, over an arbitrary field
`k : Type u`. The underlying subgroup functors and representative equality
retain all schemes, including nonreduced tests. The provenance is internal
transport and specialization of the imported Library definitions and proofs.
No structural parabolic correspondence is proved here.
