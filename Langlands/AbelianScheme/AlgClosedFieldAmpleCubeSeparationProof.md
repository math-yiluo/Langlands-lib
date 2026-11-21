# Lefschetz separation by the cube of an ample line bundle

`Langlands.AbelianScheme.algClosedFieldAmpleCubeSeparation` proves the published
`AlgClosedFieldAmpleCubeSeparationStatement` in every universe. For every ample
line bundle on an abelian scheme over an algebraically closed field, the
complete system of its tensor cube has no rational base points, separates
rational points and separates nonzero dual-number tangent vectors from their
base points.

## Implemented proof

The published theorem-of-the-square reduction gives base-point-freeness and
reduces the two separation claims to generic vanishing implications for the
complete system of the tensor square. The proof supplies both implications.
A line bundle with no rational base points has a complete generating basis,
using finiteness of its degree-zero cohomology. A nonempty open of the integral
abelian variety supplies a dense family of rational test points.

If vanishing of sections at each of those points implies vanishing at its
translate, the complete projective map agrees at the two points by
`comp_map_eq_of_rational_vanishing`. If the sections vanish along a translated
unit tangent, `comp_map_eq_of_dualNumber_vanishing` makes the projective image
of that tangent constant on the dual numbers. In either case the rational
family gives the equations for the finite closed subgroup of periods. The
translation or tangent factors through that subgroup as a point on its
respective test scheme.

The complete map descends to the finite flat abelian variety quotient by
these periods. Pullbacks of the descended projective coordinates span the
original section space. The dimension formula for ample sections forces the
quotient morphism to be an isomorphism. Since the quotient identifies the
subgroup inclusion with the unit, the given rational translation is the unit
and the given tangent at the unit is constant. These are the conclusions
of `ampleGenericTranslationVanishing` and `ampleGenericTangentVanishing`.

The proof adapts the triple-translate construction and the quotient and
section-count argument of Mumford, *Abelian Varieties*, §17, printed pp. 163–165
(PDF pp. 86–87 of `mumford-abelian-varieties-full-scan`). It descends the map of
the complete system through the common period subgroup and uses the section
count for its pulled-back projective twist.
