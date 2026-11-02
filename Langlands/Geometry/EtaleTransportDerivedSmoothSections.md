# Derived smooth sections of actual small-etale transport sheaves

This internal construction derives the actual smooth section functor
`SmoothSections.sections` using injective resolutions in the module-sheaf
category of the labelled scheme small-etale transport site. Its inputs are
`Y : Scheme.{u}`, a topological group `G : Type w`,
`ρ : G →* (Aut Y)ᵐᵒᵖ`, `Small.{u} G`, and a commutative ring
`R : Type u`. The module and representation carriers are in universe `u`;
the scheme and group universes remain independent. The source is the
existing algebraic transport-sheaf category, whose local actions need not
satisfy a continuity condition.

Write `S` for `SmoothSections.sections ρ R`. This is the constructed
global section representation functor followed by
`SmoothRep.smoothPartFunctor`. Its carrier consists of those global
sections fixed by some open subgroup of `G`. The published finite-limit
preservation and additivity of `S`, together with the abelian source and
target and enough injectives in the source, permit actual right
derivation. The smooth-part functor is not assumed exact.

`cohomology ρ R q` is `S.rightDerived q`, valued in
`SmoothRep.{u,w,u} R G`. `complex` applies `S` termwise to the chosen
transport-sheaf injective resolution. `homotopyFunctor` makes the
construction functorial in the homotopy category, and `complexIso`
identifies its value with the homotopy class of the chosen complex.
For every genuine injective resolution `I` of a transport sheaf `F`,
`cohomologyResolutionIso I q` identifies this right derived functor at
`F` with degree `q` homology of `S(I)`. This homology is computed in the
smooth representation category. Left exactness gives the natural
isomorphism `cohomologyZeroIso` with `S`. Positive-degree cohomology
vanishes on injective transport sheaves by
`isZero_cohomology_succ_of_injective`.

The bounded-below constructions explicitly assume
`HasDerivedCategory.{wS}` for the transport-sheaf category and
`HasDerivedCategory.{wT}` for the smooth representation category.
The localization universes are independent. These are Mathlib's
derived-category availability hypotheses, for which its standard
localization construction supplies realizations. They do not assume
the desired cohomology or a comparison theorem.

`rightDerivedFunctor` is Mathlib's right derived functor from the actual
bounded-below derived transport-sheaf category to
`DerivedCategory.Plus (SmoothRep.{u,w,u} R G)`. `derivedSections`
places a sheaf in degree zero and applies that functor. Thus its values
are objects of the derived category of smooth representations.

`complexPlus` extends the chosen nonnegative injective resolution by
zero to integer degrees and applies `S` termwise. It is a strict
bounded-below smooth representation complex. `resolutionIso`
identifies the derived object with the localization of the analogous
complex from any transport-sheaf injective resolution;
`complexPlusIso` selects the chosen resolution. `complexPlusMap`
applies `S` to a chosen compatible resolution lift of a sheaf map.
The two naturality equations identify these maps after localization
with the actual functorial derived-section maps. The general equation
`resolutionIso_hom_naturality` holds for every compatible morphism of
injective resolutions. Strict chosen lifts are not asserted to satisfy
functor laws before localization.

`homologyNatIso` naturally identifies the derived object's nonnegative
cohomology with `cohomology`. Its component is the generic
resolution-homology comparison for every choice of injective resolution,
as recorded by `homologyNatIso_hom_app`. `homologyZeroIso` recovers
smooth global sections. Negative cohomology of a sheaf placed in degree
zero vanishes; positive cohomology vanishes when the sheaf is injective.
The latter law transports the already proved classical vanishing
through `homologyNatIso`.

`diagramFunctor` postcomposes arbitrary diagrams of coefficient sheaves
and their natural transformations with `derivedSections`. Its indexing
category has independent object and morphism universes. This operation
forms no inverse limit and assumes no exactness of limits.

The provenance is internal specialization of Mathlib's right derived
functors and the Library's `Langlands/Cohomology/DerivedPlus.lean` and
`DerivedPlusNaturality.lean`. `EtaleTransportDerivedSections` supplies
the corresponding algebraic representation-valued pattern. The
construction reuses the actual transport-sheaf abelian structure,
chosen injective resolutions and smooth section functor; its formulas
and naturality laws apply the established generic constructions to
these source and target categories. No new theorem is attributed to
Harris or Berkovich.

This unit does not identify its cohomology with the smooth part of
ordinary or algebraic cohomology, assert that smoothing preserves
quasi-isomorphisms, or construct the full category of smooth equivariant
etale sheaves. A derived comparison with algebraic sections, supports,
analytic uniformization, arithmetic coefficients, level towers and
Harris specialization remain successor obligations.
