# Formal maps between atlases on one principal cover

This derived construction defines morphisms of actual formal O-module atlases
with the same principal-open cover, permits different finite coordinate types,
and constructs their O-linear natural transformations on nilpotent points.

## Provenance and scope

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), paragraph immediately before section 2, allows formal groups
glued over localizations of the base ring. The registered original source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
This module supplies internal morphism constructions for that convention using
`BasicAtlas`; it does not assert a separate source theorem.

O and R are arbitrary commutative rings with an O-algebra structure on R.
The coordinate types are fixed finite types in `Type`. Coefficient test
R-algebras lie in R's universe v, and compatible-family point modules lie
in v+1. Source and target have equal sets of principal-open generators.
The equality is an explicit parameter; `sourceChart` preserves the generator
while transferring its membership proof.

The formal maps are supplied as actual O-linear power-series homomorphisms
over every coefficient test algebra in a chart, with formal naturality and
transition compatibility equations. They are not arbitrary maps of point
carriers. The result constructs the induced point maps from these data.
It does not prove that every natural point transformation is formal, or give
maps or comparisons between different covers, refinement invariance, a formal
scheme comparison, a moduli object or representability.

## Formal maps and their evaluation

`Hom X Y h` has one actual formal O-linear homomorphism for each test algebra
and target chart where the generator is invertible. Its source is the
corresponding extended X chart and its target the extended Y chart.
`natural` equates coefficient extension of its coordinate series with the
coordinate series at the new test algebra. `transition` says that changing
the target chart after the map equals changing the source chart before it.
`Hom.ext` reduces equality of these structures to equality of all formal maps.

`onChart_natural` derives the coefficient square on nilpotent tuples from
`SeriesPoint.map_eval` and the formal naturality equation. `onChart_transition`
evaluates the formal transition equation and uses the evaluation formula
for composition.

`onPoints f A` applies these formal maps to the components of a compatible
family. The first tuple square and the source family's coefficient equation
prove coefficient compatibility of its image. The second square and the
source family's transition equation prove chart compatibility. Linearity
holds at every component because every formal map is O-linear.
`onPoints_apply` records the component formula.

`onPoints_natural` proves that this operation commutes with the precomposition
that defines coefficient extension of families: both sides have the same
component. `pointNatTrans` packages these proved maps and equations into a
natural transformation between the previously constructed module-valued
point functors.

## Identity and composition

`id` uses the identity formal map in each chart. `comp` composes formal maps
over each test algebra. Preservation of composition under coefficient
extension proves its naturality. Associativity of formal composition and
the two supplied transition squares prove its transition equation.
`onPoints_id` and `onPoints_comp` verify the corresponding operations on
constructed points by componentwise evaluation.

`comp_id`, `id_comp` and `comp_assoc` prove the identity and associativity
laws for actual formal atlas morphisms using `Hom.ext` and the respective
laws for formal O-linear maps. Proof irrelevance identifies the different
proofs of equality of covers and membership of the same generator.
