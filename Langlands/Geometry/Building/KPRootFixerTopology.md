# Compact root-fixer intersections and finite root products

This derived unit uses the actual root filtrations of a
`ValuationBuildingData` over an arbitrary-universe nonarchimedean local field.
It keeps the canonical `rationalPointTopology F G.X` and the root-group
subspace topology. Its only additional hypothesis is the existing V 7
predicate `B.apartment.IsTopologyCompatible`.

The strict-depth subgroup contains the V 7 open subgroup at depth `r + 1`,
so it is open in its root group. Since that root group is ambient closed,
the strict-depth subgroup is also ambient closed. Its containment in the
compact weak-depth filtration at `r` then proves compactness. No discreteness
of the valuation jumps is assumed.

Each root fixer is an intersection of ambient closed filtrations with the
closed actual root group. The strict variant uses the same argument. For a
nonempty apartment subset, either fixer is a closed subset of one compact
root filtration and is therefore compact. The subset need not be a facet,
finite, or bounded. The compactness claims explicitly require a point in it;
no compactness claim is made for the empty-subset root group.

The point blocks at depths `0` and `0+`, and both facet blocks over any
nonempty subset, are compact products of their two actual factors.
The doubled-root factor is retained whenever it is a relative root, and is
the trivial subgroup exactly when it is absent.

The existing ordered filtration, chamber, and facet block multiplication
maps are continuous: each coordinate inclusion is continuous, and their
finite ordered list product is continuous in the canonical topological
group. These continuity results apply to arbitrary character lists and
do not require V 7. For lists of actual relative roots, the factors proved
compact above give compact product domains and hence compact ranges.
The facet range compactness keeps the explicit point in the subset.
All finite lengths, including zero, and both Boolean depth choices are
retained; there is no sign, ordering, distinctness, or enumeration premise.
There is also no assertion that any such range is a subgroup or is equal
to the generated sharp fixer.

## Provenance

The constructions are the published `KPRootFixerPlus`, `ChamberRootProducts`
and `KPFiltrationTopology` objects. The argument is a derived consequence of
their membership laws, V 7, and ordinary topological-group results; it does
not assume a source compactness assertion or replace any subgroup.

KP, *Bruhat–Tits Theory: A New Approach* (2023), Definition 6.1.2, printed
p.199 / PDF p.230, gives V 7 and the strict-depth union convention.
Definition 7.4.1(1), printed p.255 / PDF p.286, gives the root-fixer
intersection. These source conventions motivate the imported constructions.
The authors' 1 November 2024 corrections, PDF pp.33–35, add AS 5 to the
Chapter 7 standing assumptions and simplify singleton notation. The present
topological argument uses V 7 directly and needs no Chapter 7 decomposition.

This unit proves compactness of individual factors and of finite product
ranges. Compactness or openness of the sharp generated subgroup, the full
parahoric, and the actual chamber Iwahori remain separate obligations.
