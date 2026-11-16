# Étaleness of open analytic domain inclusions

The theorem
`Langlands.Analytic.SaturatedAtlasPresentation.etaleOpenDomainStatement`
proves the existing `EtaleOpenDomainStatement`: for every localized analytic
space `X`, every open subset `U`, and a proof that `U` is open, the actual
canonical inclusion `domainι X ((presentationOf X).openDomain U hU)` is étale.
It is uniform in universe parameters `u` and `v` and in the complete
ultrametric normed field `K`. It uses the published all-affinoid-pieces
predicate `etale` and the existing open-domain construction.

This is an internal derived proof of the Library statement. Its provenance is
the existing atlas, domain, full-recognition, and localization constructions;
it introduces no translation from external literature and assumes no unproved
geometric proposition. The statement and its imported modules are unchanged.

## Bounded maps on chart pairs

The private predicate `RepresentsCharts` says that each admissible bounded
chart pullback represents its actual image locus. The proof of its composition
law uses the universal property for composition of represented domains and
change of target chart. Injectivity of the second ambient map gives injectivity
of the intermediate spectrum map, using the chart commutation laws and the
embedding of the intermediate chart. For a domain inclusion the pullbacks are
the ambient atlas restrictions, which already represent the relative chart
domains.

The map `saturatedInclusion` conjugates the actual domain inclusion by the
source and target saturation isomorphisms, producing a strong map between
constructed saturations. The saturation comparison maps represent their chart
image loci, so composition proves the same property for this map. Its ambient
map is still the subspace inclusion.

## Finite étaleness over the domain

The helper `pair_equiv` compares a recognized target piece with the recognized
source piece associated to one source chart. Assume the image of that source
chart and the range of a target chart both equal the recognized target locus.
The target recognized-to-chart restriction and the strong chart pullback then
represent whole spectra, hence supply bounded algebra equivalences. Together
with the canonical equivalence from an original recognized source piece to its
source chart, they give an equivalence on the recognized pair.

Its forward bounded map is proved equal to the full-recognition pair-system
pullback using `originalRestriction_comp_fullRecognitionPairs` and cancellation
of the source restriction equivalence. Thus the argument compares the complete
bounded algebra maps, rather than recovering algebra maps from spectrum-point
maps.

For `B = ofFullRecognition P`, full-recognition idempotence supplies an original
`B` chart whose range is any given recognized piece `W` of the saturation of
`B`. If `W` lies inside the analytic domain `D`, this chart is also an original
chart of the actual subspace atlas of `D`. Choose those two original charts in
their saturations and recognize the source chart. Its locus is precisely the
preimage of `W`, and its image is `W`. Applying `pair_equiv` gives a bounded
algebra equivalence for the actual pair-system pullback.

A bounded equivalence is finite as a Banach module map: the single generator
is `1`, the coefficient of `y` is its image under the bounded inverse, and the
inverse bound supplies the coefficient norm bound. Its bijective ring map is
also algebraically finite étale. This proves `IsFiniteEtaleOver univ D.carrier`
for `saturatedInclusion B D`.

## The canonical localized inclusion

When `D` is the open subset `U`, the preceding finite-étale-over assertion
provides local finite étaleness at every source point, with open neighborhoods
`univ` and `U`. The published reduction
`IsLocallyFiniteEtaleAt.isEtaleAtAllPieces` gives the required strong all-pieces
étaleness. The localized saturation isomorphisms give an arrow isomorphism to
`B.localizedDomainInclusion D`; its square commutes by cancellation of the
saturation inverse and hom. This proves
`etale_openDomain_fullRecognition`.

Finally, the helper module [Transport](Transport.md) restricts ambient
isomorphisms to corresponding domains, proves an isomorphism of their actual
canonical inclusion arrows by the domain factorization laws, and transports
étaleness through it. Every localized analytic space is isomorphic to a
full-recognition presentation through the saturation comparison and the
canonical full-recognition quasi-isomorphism. Applying this transport theorem
to `etale_openDomain_fullRecognition` proves the exact target.
