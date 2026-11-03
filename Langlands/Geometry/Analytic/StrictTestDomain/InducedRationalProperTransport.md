# Proper transport of actual induced rational spectra

This internal construction restricts the existing rational transport category
by properness of its actual induced continuous map of balanced quotient
spectra. The complete ultrametric normed field and presented strict affinoid
algebra use universe `u`; the topological group has independent universe `v`.
No new spaces, rational-domain maps, group labels or actions are supplied.

`properInducedMap` tests `IsProperMap f.inducedMap`. Its multiplicativity
instance uses the existing proofs for the identity and composite induced
maps. Mathlib's `WideSubcategory` therefore constructs `ProperTransport`,
with every original object and precisely those original arrows whose actual
induced map is proper. `properTransportInclusion` is faithful.

`SmoothProperTransport` is Mathlib's full subcategory of this category on the
objects whose actual induced spectra have stable neighbourhoods for the
group action. Its object property supplies that instance. `transport` and
`Hom.transport` recover the original objects and arrows; `ofTransport` and
`Hom.ofTransport` include any original object with that property and any
proper original arrow between them. The latter recovery is definitional,
as are recovery of identity and composition. The forgetful functor is
faithful. `spectrumDiagram` restricts the already constructed diagram of
continuous full-group actions to this category.

The provenance is internal application of Mathlib's wide and full
subcategory constructions to the published induced rational transport
maps. Properness and stable neighbourhoods remain predicates selecting the
objects and arrows. This does not prove that every rational transport map
is proper or that every induced spectrum has stable neighbourhoods. It
asserts no analytic etale realization, uniformization or Shimura
specialization.
