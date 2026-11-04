# Proper adelic scheme points and the full local product

Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p.10, Example 4.3, identifies adelic projective points with
the full product of local projective points, using the equality of integral
and field points at every nonarchimedean place. This target states the
proper-scheme extension of that comparison. The extension is derived from
the proper spreading and valuative arguments in printed p.11, Proposition
4.4, together with Theorems 3.4 and 3.6; the source does not separately name
this general full-product assertion.

`AdelicProperAllPlaceStatement` requires that the actual all-place map be
a homeomorphism in both characteristics. In the curve branch k is a finite
field and F is a function field over k with the compatible supplied
RatFunc k-algebra structure. In the number branch K is an arbitrary number
field and all infinite factors are included. All schemes and coefficient
rings lie in an arbitrary common universe.

A finite set S, a finite-type scheme X over the actual outside-S integer
ring, and an isomorphism e from its actual generic fiber to Y are supplied.
Finite type is expressed by `LocallyOfFiniteType X.hom` and
`QuasiCompact X.hom`. The scheme Y is proper over the original global
field. The supplied model X need not be proper or separated. Its topology
is the published `SpreadAdelePointTopology`, transported from arithmetic
levels through e; it is not replaced with the chart topology on points
valued in the nonlocal adele ring.

The target is the independently defined `LocalPointTopology`: an ordinary
product of the local affine-chart point topologies on actual local field
points. The map is exactly `curvePlaceAdelePointMap` or
`numberFieldAdelePointMap`, with the original adelic coordinate projections.
`IsHomeomorph` asserts continuity, openness and bijectivity of that map.
There is no assumed local integrality, bijection, continuity, topology
agreement, or proper arithmetic model in the hypotheses. Constructing a
proper spread, applying valuative extension, and comparing the resulting
maps and topologies are proof obligations.

Specialization to actual projective space supplies the full-product part
of Example 4.3 once its properness and actual model are installed. The
rational-point density assertion and the affine-line subspace-topology
assertion in that example are separate obligations. This module states
the comparison; it does not supply its proof or an existence theorem for
the input spread.
