# Actual point comparison for every cover of a global formal module

`BasicAtlas.globalCoverPointEquiv` constructs an O-linear equivalence between
`(BasicAtlas.ofGlobalCover M s hs).Point A` and `M.AlgebraPoint A` for any
principal-open cover. Its inverse restricts a global tuple to every chart test;
its forward map actually glues localized nilpotent tuples in A. Both inverse
equations and coefficient naturality are proved.

## Provenance and scope

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109,
paragraph immediately before section 2 (PDF page 3), permits formal groups
obtained by gluing formal groups over localizations of the base. The registered
source is `drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The original paragraph motivates the atlas interface. This comparison is
derived infrastructure, not a separately stated theorem in that source.

O and R are arbitrary commutative rings, R is an O-algebra, σ is a finite
coordinate type in `Type`, and M is a fixed global formal O-module law over R.
The set s of generators spans the unit ideal and can be infinite. A ranges
over commutative R-algebras in the universe v of R. The compatible-family
carrier has universe v + 1; the original algebra-point carrier has universe v.
All points in this unit use `Empty` as formal-variable type, so their actual
coordinate tuples are nilpotent tuples, as in the published point interface.

The construction proves independence of the principal cover for a fixed
global law. It does not construct descent or refinement for arbitrary varying
chart laws, a quotient of all atlases, arbitrary-site sheaf conditions, framing,
heights, moduli, representability, or levels. No reducedness, Noetherian
hypothesis, flatness assumption, injective coefficient map, or uniform bound
on local nilpotence exponents is required.

## Restricting the global law

Write X for `ofGlobalCover M s hs`. Its charts are the restrictions of M and
its transitions are the identity-coordinate isomorphisms already constructed
in `GlobalAtlas`. `globalCover_transitionPoints` proves that evaluation of
such a transition fixes its raw nilpotent tuple. Consequently
`globalCover_chart_independent` proves that the components of an actual atlas
point over the same test algebra and test map agree in all available charts.
This is a consequence of the atlas compatibility equation, not an extra
assumption on the family.

`globalCoverComponent` takes a coefficient-algebra map A → B and a chart
defined over B. It composes `M.algebraMapPoints` with the inverse of the
actual `globalChartIso` over B. Its underlying function is coefficient change
on the raw tuple, by `globalCoverComponent_apply`. The copied linear map
`globalCoverComponentMap` exposes that function while retaining the proved
linearity for the actual formal addition and scalar action.

`toGlobalCoverPoints` restricts each global point at every chart test. The
coefficient compatibility follows from composition of tuple coefficient maps;
the chart compatibility follows from the identity-coordinate transitions.
The component linear maps prove O-linearity. `toGlobalCoverPoints_apply`
records the raw restriction formula at every test.

## Constructing the global tuple

The image generators `(algebraMap R A) '' s` cover A: the reused
`baseOpens_covers` maps the unit-ideal span identity to A. The reused
`baseSource` chooses an original chart above each image generator; neither
existence nor uniqueness of that preimage is assumed. For an image generator
b, `imageCoverTest` is the test A → A[1/b] in that chosen original chart. Its
unit proof uses `baseSource_image` through `baseChartCoefficient_unit`.

`globalCoverLocalFamily` evaluates the given actual atlas point at those
tests. `globalCoverLocalFamily_compatible` proves the raw pairwise overlap
equations required by `SeriesPoint.BasicCompatible`. For b and c it constructs
the actual restriction maps from A[1/b] and A[1/c] to A[1/(bc)]. Their
equalities on A show that the two composite test maps are the same. The
family's coefficient naturality identifies the restricted tuples with its
overlap-test components; `globalCover_chart_independent` identifies those
components even when the chosen original charts differ.

`fromGlobalCoverPoints` applies the previously constructed
`SeriesPoint.glueBasic` to this family. That construction glues every
power-series coefficient and proves substitutability by detecting nilpotence
of the constant coefficients on the principal cover. Thus this definition
constructs an actual global nilpotent tuple without taking any gluing operator
or comparison isomorphism as an input.

`fromGlobalCoverPoints_map` recovers the prescribed tuple at the canonical
localization of every original chart. To prove it, the gluing formula is
applied to the image of that chart's generator. Its chosen preimage need not
be the original generator; chart independence identifies their components in
the same actual localization. This also handles two distinct original
generators with the same image in A.

## Inverses, naturality, and cover comparison

`from_toGlobalCoverPoints` uses separation on the image cover and the explicit
gluing restriction formula to recover every global point.
`to_fromGlobalCoverPoints` uses `ext_localTests` and
`fromGlobalCoverPoints_map` to recover the full atlas family. The resulting
`globalCoverPointEquiv` is the inverse of the O-linear restriction map, so
its gluing direction is O-linear as well.

`globalCoverPointEquiv_apply` identifies its forward map with the constructed
gluing. `globalCoverPointEquiv_symm_apply` gives its inverse at every test.
`globalCoverPointEquiv_component` proves that restricting the glued tuple
along any test map gives exactly that test's prescribed component.

`toGlobalCoverPoints_natural` follows from coefficient-map composition on
each test. Applying the inverse equivalences gives
`globalCoverPointEquiv_natural`, including naturality of the gluing despite
the choices of original charts. `globalCoverPointFunctorIso` assembles these
maps into a natural isomorphism to the original algebra-point functor with
the necessary module universe lift. `globalCoverNilpPointFunctorIso`
restricts this isomorphism to the actual category where a specified π is
nilpotent. Finally, `globalCoverComparisonFunctorIso` composes the comparison
for one cover with the inverse comparison for another: any two principal
covers of the same global law give naturally isomorphic actual point functors.
