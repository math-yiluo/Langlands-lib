# Actual adelic units with divergent inverses

This is a derived construction for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (2011), printed pp.3–4, where the unit group of
an adelic ring fails to have continuous inversion in the subspace topology.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
SHA256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad does not specify a sequence; the uniformizer sequence here is an explicit
realization of his obstruction.

For a family of fields with subrings, `restrictedUnitAtPlace` puts a chosen
nonzero integral value at one place and puts one elsewhere. It is an actual
unit of the cofinite restricted product: both the tuple and its coordinatewise
inverse are integral except possibly at the single exceptional place.
The coordinate formulas describe both the value and its exceptional inverse.

Distinct exceptional places give convergence of the values to one in the
original restricted-product topology. The proof first establishes coordinate
convergence in the product of the integral subrings, then uses the continuous
inclusion of this whole integral product into the restricted product.
When all subrings are open and each chosen inverse is nonintegral, the inverses
cannot converge to one: the open set of tuples integral at every place contains
one and contains no term of the inverse sequence.

`adicIntegralNonunit` maps a uniformizer into the actual completed valuation
ring associated with a height-one prime of a Dedekind domain. The extended
valuation is `WithZero.exp (-1)`, so this element is nonzero and its inverse
is nonintegral.

`numberFieldUnitSequence` uses the proved infinitude of actual finite places
of a number field, keeps every infinite coordinate equal to one, and applies
this construction at the finite places. Its values tend to one in the full
adelic ring; its inverse values do not. `curvePlaceUnitSequence` proves the
same assertions at actual discrete curve places of a finite extension of
`RatFunc k`, over arbitrary constants and with no separability assumption.
The published place infinitude theorems supply the distinct-place sequences.
The arbitrary common arithmetic universe and the original arithmetic topology
instances are retained.

This unit supplies the sequences and their intrinsic properties. The failure
of topological embedding for the unit inclusion and its comparison to actual
punctured-affine-line scheme points are separate consequences.
