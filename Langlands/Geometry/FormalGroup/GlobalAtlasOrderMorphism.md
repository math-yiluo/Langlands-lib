# Global order-linear formal maps and their atlas restrictions

This derived unit restricts actual order-linear formal maps to principal-open
atlases. It proves that the singleton order-linear point comparison intertwines
these maps, including on the nilpotent coefficient category.

## Provenance and scope

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), permits formal groups glued over localizations in the paragraph
before section 2 and defines formal O_D-modules in section 2 A. The registered
original is `drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The present unit is an internal consequence of the actual formal maps and
identity-coordinate chart comparisons in `OrderAction`,
`GlobalAtlasMorphism`, `GlobalAtlasOrderAction` and `AtlasOrderMorphism`.
It does not identify a new numbered theorem of the source.

O and R are arbitrary commutative rings, R is an O-algebra and D is a possibly
noncommutative O-algebra. The source and target coordinate types are fixed
finite types in `Type` and can differ. Coefficient algebras have R's universe v;
their original point modules lie in v and atlas families lie in v+1.
Restriction uses a supplied common principal-open cover with
`Ideal.span s = top`. The comparison with the original point map is for the
singleton cover at 1. General cover comparisons, refinements, full
faithfulness, specialness, heights, formal-scheme comparisons, moduli and
representability remain outside this unit.

## Evaluating the original order-linear maps

`ModuleLaw.OrderAction.Hom.onAlgebraPoints f A` extends the actual formal map
along the structural O-algebra map from R to A and evaluates it. Existing formal
order commutation proves D-linearity. `onAlgebraPoints_natural` follows from
the underlying O-linear formal map's coefficient naturality.
`algebraPointNatTrans` packages this into a D-module natural transformation,
and `nilpAlgebraPointNatTrans` restricts it along `Nilp.forget`.

`onAlgebraPoints_id` and `onAlgebraPoints_comp` give the identity and
composition formulas by evaluation of the extended formal maps.
`ModuleLaw.OrderAction.Iso.onAlgebraPoints` extends both actual inverse maps
and evaluates the resulting formal isomorphism. `algebraPointNatIso` uses
these D-linear equivalences and the preceding naturality equation;
`nilpAlgebraPointNatIso` restricts it to Nilp. No point equivalence is supplied
as independent input.

## Restriction to the atlas

`BasicAtlas.globalOrderChartHom` first applies the actual order-linear
comparison from the restricted source chart to the directly extended global
source. It applies the extended global map and returns to the target chart
with the inverse target comparison. `globalOrderChartHom_val` identifies its
underlying formal O-linear map with `globalChartHom`.

`ofGlobalOrderHom` keeps the existing actual atlas map `ofGlobalHom`.
The formal commutation equation with every element of D is exactly the
equation already proved for `globalOrderChartHom`. Thus the construction
retains coefficient naturality and transition compatibility of the formal
chart maps, as well as their full order linearity.

`ofGlobalOrderHom_id` and `ofGlobalOrderHom_comp` follow from equality of
the underlying actual formal atlas maps. `ofGlobalOrderIso` restricts both
actual inverse maps; preservation of composition and identity proves its
formal inverse equations.

## Compatibility of the singleton comparison

`globalOrderPointEquiv_ofGlobalOrderHom` states that applying the atlas map
and then the target D-linear singleton comparison equals applying the
original formal map to the source comparison. The underlying tuple
functions are the ones in the already proved O-linear comparison, which
proves this equation.

`globalOrderPointFunctorIso_natural` states the same square as an equality
of D-module natural transformations. The original natural transformation
is followed by `ModuleCat.uliftFunctor` to match the atlas family universe.
Extensionality reduces the square to the preceding point equation under
`ULift.up`. `globalOrderNilpPointFunctorIso_natural` evaluates this same
equality on the underlying coefficient algebra of each Nilp object.
