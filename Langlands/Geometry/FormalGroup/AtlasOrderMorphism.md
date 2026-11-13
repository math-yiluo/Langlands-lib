# Order-linear maps of formal coordinate atlases

This derived unit implements actual order-linear formal maps on a fixed
principal-open cover and their maps on compatible nilpotent families.

## Provenance and scope

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), permits formal groups glued over localizations in the paragraph
before section 2 and defines formal O_D-modules in section 2 A. The original
source is `drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The constructions here are internal consequences of `AtlasMorphism`,
`AtlasOrderAction` and `OrderAction`. They implement morphisms in this local
coordinate convention; they are not separately numbered source theorems.

O and R are commutative rings, R is an O-algebra, and D is any possibly
noncommutative O-algebra. Each atlas has a fixed finite coordinate type in
`Type`; the two types may differ. The source and target have equal sets of
principal-open generators, with the equality supplied explicitly. Coefficient
tests lie in R's universe v and family carriers in v+1. No change of cover,
refinement invariance, formal-scheme comparison, specialness, height, moduli
object or representability is asserted.

## Formal maps and their evaluation

`BasicAtlas.OrderAction.Hom E E' h` is a subtype of the existing actual
`BasicAtlas.Hom X Y h`. Its condition requires every formal chart map to
commute with every order element, as an equality of actual coefficient-extended
formal homomorphisms. The inherited map already has formal coefficient
naturality and transition compatibility. `Hom.commutes` exposes this equation,
and `onChart` packages the chart map as a global order-linear formal map over
the test algebra.

`onPoints` retains the existing componentwise map on compatible families.
Its D-linearity follows at each chart test by evaluating `onChart`.
`onPoints_apply` gives this component formula, and `chartEquiv_onPoints`
states that the constructed D-linear chart comparison intertwines the family
map with the actual order-linear chart map. `onPoints_natural` reuses the
coefficient naturality of the underlying family map. `pointNatTrans`
packages these maps between the actual D-module point functors, and
`nilpPointNatTrans` restricts along the inclusion of Nilp.

`Hom.id` and `comp` use identity and composition of the underlying actual
formal atlas maps. The order-commutation equation for a composite follows
by associativity and the two constituent commutation equations. The formal
identity and associativity laws follow from the underlying atlas-map laws.
`onPoints_id` and `onPoints_comp` prove that evaluation preserves these
operations.

## Actual inverse maps

`Iso E E' h` consists of two actual order-linear atlas maps with inverse
equations in the formal Hom types. `Iso.onPoints` constructs a D-linear
equivalence by evaluating the two maps; its inverse laws follow by evaluation
of the formal inverse equations. `pointNatIso` uses these equivalences and
the already proved coefficient naturality, and `nilpPointNatIso` restricts
that isomorphism to Nilp. `refl`, `symm` and `trans` construct identity,
reverse and composite actual atlas isomorphisms.
