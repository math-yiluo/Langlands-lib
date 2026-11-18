# Pointed local affine etale limits and localization

Worker 875.

`Langlands.AlgebraicGeometry.LocalEtaleLimit S s` records a local ring, a
small cofiltered diagram of affine schemes etale over `S`, and an actual
limiting cone whose point is the spectrum of that local ring. The cone has a
compatible map to `S` sending the closed point to `s`. The ring need not be
Henselian or have separably closed residue field. There is no universal
property beyond the recorded diagram limit.

`StrictLocalEtaleLimit.toLocal` forgets the two additional ring properties of
the published strict-local data interface. It keeps every scheme, map, cone
and point equation unchanged.

`LocalEtaleLimit.ofLocalization R p` is an actual construction for every
commutative ring `R` in universe `u` and prime `p`: its local ring is
`Localization.AtPrime p.asIdeal`, its index is the opposite of the elements
outside `p` preordered by divisibility, and its levels are spectra of the
basic localizations `R[1/a]` for `a` outside `p`. These levels are affine and
their structural maps are open immersions, hence etale.

The implementation uses the published `UnramifiedFunctor.Charts.awayDiagram`,
`awayCocone` and `awayCoconeIsColimit`. Forgetting from rings under `R` preserves
this colimit, and applying the contravariant spectrum functor gives the actual
limiting cone of schemes. The localization-map equations prove compatibility
with the structural maps. The maximal ideal of the local ring contracts to
`p`, proving the image of its closed point. `ofLocalization_baseMap` records
that the map to `Spec R` is the canonical localization spectrum map.

These are internal definitions and consequences of the published localization
colimit construction and Mathlib's spectrum and localization facts. No
strict-henselization construction or existence theorem is invoked. The data
supports spreading finitely presented objects from ordinary local rings.
