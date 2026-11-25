# Agreement of local opposite Borels on étale overlaps

This module uses the relative uniqueness lemma of
`OppositeBorelRelativeUniqueness` and the Borel transport lemmas of
`BorelEtaleTransport`.

This module retains `RelativeParabolicLieContainmentStatement` as an explicit
premise. It does not discharge that statement.

`IsFibrewiseMaximalTorus.baseChange` transports residue-fibre maximality through
an arbitrary base change when the original ambient group is smooth and affine.
The original predicate gives maximality at every field-valued point by the
published field-point theorem. The comparison between a composite pullback and
successive pullbacks gives maximality at each new residue fibre.

`oppositeBorel_intersection_baseChange_comparison` pulls back an all-test
intersection equality and transports it to the direct ambient pullback.
It uses base change of ranges and intersections, inverse-image transport under
an ambient isomorphism, and naturality of the canonical pullback comparison.

`oppositeBorel_overlap_range_eq` assumes a reductive ambient group, the original
relative Borel and maximal torus, and actual local relative Borel inclusions
whose intersections with the original Borel pullbacks equal the torus
pullbacks. On the overlap of any two members of the étale cover, both local
Borels remain relative Borels and both intersection equalities remain valid.
After transporting them to the common direct ambient pullback, the relative
uniqueness lemma gives equality of their ranges on all test schemes.

This is a derived implementation of the matching argument in the descent step
of Conrad, *Reductive group schemes* (2014), Proposition 5.2.12, p.158.

Shared declarations `IsFibrewiseMaximalTorus.baseChange` are imported from `Langlands.GroupScheme.Torus.FibrewiseMaximalTransport`; their mathematical hypotheses, conclusions and data are unchanged.
