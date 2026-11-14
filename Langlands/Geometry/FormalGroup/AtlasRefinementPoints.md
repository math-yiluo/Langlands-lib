# Actual point descent along a principal-cover refinement

`BasicAtlas.CoverRefinement.pointEquiv` identifies the actual compatible point
families of a formal O-module atlas with those of its constructed finer
restriction. Its forward map is the restriction in `AtlasRefinement`; its
inverse glues actual nilpotent tuples separately in each original chart.
Both inverse identities and naturality are proved.

## Provenance and scope

This is derived infrastructure for Drinfeld's convention that formal groups
may be glued from formal groups over localizations: Drinfeld, *Coverings of
p-adic symmetric regions* (1976), printed p.109, paragraph immediately before
section 2 (PDF page 3). The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The point comparison constructed here is not a separate theorem attributed
to that paragraph.

O and R are arbitrary commutative rings, with an O-algebra structure on R.
The coordinate type is finite in `Type`, and test R-algebras lie in R's
universe v. Original chart laws may vary. Both principal covers may be
infinite. The refinement data in `AtlasRefinement` consist of a finer cover,
a chosen original chart for each finer generator, and proof that its
original generator becomes a unit in the finer localization. The finer laws
are the constructed coefficient restrictions in the same coordinates.

No global formal law, supplied point equivalence, supplied gluing operator,
or uniform bound on local nilpotence exponents is assumed. This comparison
does not construct arbitrary coordinate comparisons between atlas
presentations, a quotient of atlases, framing, heights, a moduli problem or
a representing formal scheme.

## Local transport and actual gluing

`transportedValue` evaluates a finer-chart component and uses the original
atlas transition to express it in any original chart available over that
test. `transportedValue_natural` and its underlying-tuple form
`transportedValue_map` follow from coefficient naturality of the original
transitions and the finer family's coefficient equation.
`transportedValue_independent` uses the finer family's transition equation
and the original cocycle to prove independence of the chosen finer chart.
`transportedValue_transition` is the original cocycle equation.

For an original test t with target B, `imageTest B c` is a finer-chart test
over B[1/c], where c runs through the image of the finer generators in B.
This image spans the unit ideal. `localFamily` transports its finer tuples
into the original chart t.chart. `localFamily_compatible` constructs the
two actual coefficient maps to B[1/(c*c')]. Naturality identifies the two
restricted tuples with their transported values there; independence of the
finer chart then gives equality.

`gluedValue` applies `SeriesPoint.glueBasic` to this matching family. That
construction glues each coefficient by the localization theorem and proves
substitutability by detecting coordinate constant-term nilpotence on the
cover. `gluedValue_local` records its value in every cover localization.

## Recovery and compatible families

`gluedValue_map` proves recovery under any coefficient map B to C for which
the original chart and a finer chart b are available. The map factors
through B[1/image(b)] by the localization universal property. The local
gluing equation followed by transport naturality computes its value;
independence of the chosen finer chart identifies it with the component
indexed by b. The image cover requires no injectivity on generators, and
its chosen source generator need not be b.

`gluedValue_natural` compares coefficient maps after localization on the
finer image cover of the target. The recovery equation makes both tuples
equal there. `gluedValue_transition` uses the same cover, transition
naturality and `transportedValue_transition`. Thus
`gluedValue_compatible` proves both equations required for an original
atlas family, and `fromPoints` packages the constructed family.

`gluedValue_onPoints` compares the reconstructed tuple with each component
of an original family on the image cover. Its chart and coefficient
compatibility equations identify both local values. `from_onPoints`
therefore proves the left inverse on full families. `on_fromPoints` applies
`gluedValue_map` to the identity coefficient map and the given finer chart;
the original self-transition gives the right inverse at every finer test.

## Linear and natural comparisons

`pointEquiv A` combines the already proved O-linear restriction with
`fromPoints` and the two inverse identities. This establishes linearity for
the actual formal-law addition and O-action; no coordinatewise additive
structure is substituted. Its two application lemmas describe both
functions at every test.

`pointEquiv_natural` is restriction naturality. Injectivity of that
equivalence and its right inverse prove `fromPoints_natural`.
`pointFunctorIso` packages the equivalences as an isomorphism of the actual
module-valued point functors. `nilpPointFunctorIso π` restricts it along
`Nilp.forget R π`, so it applies to actual R-algebras where the image of π is
nilpotent, without any additional hypotheses on π.
