# Order actions on formal coordinate atlases

This derived construction equips the compatible nilpotent points of an actual
formal coordinate atlas with a possibly noncommutative order action.

## Provenance and scope

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), first extends formal groups to objects glued over localizations
in the paragraph immediately before section 2, then defines formal O_D-modules
in section 2 A. The registered original source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The constructions here are internal consequences of `OrderAction`, `BasicAtlas`
and `AtlasMorphism`, implementing the order action in that local-coordinate
convention. They are not additional numbered source theorems.

O and R are commutative rings, R is an O-algebra, and D is any possibly
noncommutative O-algebra. D is not assumed to be a division order here.
The coordinate type is a fixed finite type in `Type`. Coefficient test
algebras have R's universe v; compatible-family carriers lie in v+1.
No special tangent-character condition, dimension or height constraint,
refinement invariance, comparison with all formal schemes, moduli object
or representability is asserted.

## Actual chart actions and their transitions

`BasicAtlas.OrderAction D X` supplies an existing formal `OrderAction` on
each law `X.chart b` over R[1/b]. These are unital ring maps into actual
formal O-linear endomorphisms, extending the given O-action. For every test
algebra where two generators become units, the structure requires the
formal transition map to commute with the two extended order actions.
This is an equality of actual formal homomorphisms, not a condition on
unrelated modules or arbitrary functions.

`endomorphism a` constructs a formal atlas endomorphism for each a in D.
Its chart map is the coefficient extension of the chart's actual formal
endomorphism. Naturality follows from composition of coefficient extension
and uniqueness of the localization coefficient map. Its transition square
is precisely the supplied formal compatibility equation. The existing
`Hom.onPoints` construction therefore preserves the simultaneous
coefficient and transition equations on compatible families.

## The constructed point action

`Point E B` has the same underlying compatible families and additive group
as `X.Point B`. The D-action applies `endomorphism a` to those families.
`smul_apply` computes every component using the actual extended formal
endomorphism of that chart. The module laws follow componentwise from the
ring laws of the chart action and formal evaluation of identities,
composition, addition and zero. `scalar_point` proves that restriction
along O to D recovers the original O-action on compatible families.

`mapPoints` uses the original coefficient map on families and proves its
D-linearity from naturality of the constructed atlas endomorphism.
`pointFunctor` packages these maps as a functor to D-modules;
`nilpPointFunctor` restricts it to algebras in which the image of a supplied
base element pi is nilpotent. Identity and composition use the already
proved family coefficient-map laws.

`ChartPoint` is the nilpotent-point module of the actual extended chart
order action. `evaluation` at any chart test is D-linear: the component
formula for the action gives its scalar equation definitionally. When b
is a unit over B, `chartEquiv` upgrades the existing O-linear chart
equivalence to a D-linear equivalence by using this evaluation map and its
already proved bijectivity. Thus the local point comparison also respects
the full order action.
