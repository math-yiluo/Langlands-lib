# Uniqueness of an opposite relative Borel through a maximal torus

This module uses the field uniqueness proof of `OppositeBorelFieldUniqueness`.

This internal reduction implements the uniqueness argument in Conrad,
*Reductive group schemes* (2014), Proposition 5.2.12, p.158. It does not prove the existence of an
opposite relative Borel or discharge `RelativeParabolicLieContainmentStatement`.

`oppositeRelativeBorel_residueFiber_range_eq` assumes a reductive group scheme
over an arbitrary base, a fibrewise maximal torus, and three relative Borel
subgroups. The two candidate opposites intersect the fixed Borel in the
supplied torus as subgroup functors on every test scheme. It proves equality
of their images on each actual residue-field fibre. The proof pulls back both
intersection equalities, using that ranges and intersections commute with
base change. Reductivity supplies a connected reductive residue fibre,
fibrewise maximality supplies the maximal torus there, and the relative Borel
predicates supply geometric Borelness. `oppositeGeometricBorel_range_eq`
(`OppositeBorelFieldUniqueness`) then gives equality on that fibre.

`oppositeRelativeBorel_range_eq` adds the relative torus and closed subgroup
hypotheses from the opposite Borel target. It takes the full
`RelativeParabolicLieContainmentStatement` as an explicit premise. The
intersection equalities imply that both candidate Borels contain the given
torus. The preceding fibre equality and
`relativeParabolic_range_eq_of_residueFiber_range_eq` then prove equality of
the candidate images on every test scheme over the original base, including
nonreduced tests.

The source reduces uniqueness to fibres by Corollary 5.2.7(2), p.155, and then
uses the field uniqueness in Proposition 1.4.4, pp.32–34. This module follows
that route. The Lie-containment premise is precisely the retained spreading
input. No additional hypothesis on the base is imposed.
