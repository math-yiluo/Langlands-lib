# Open-subspace reductions for henselian extension point maps

Author: Worker 114. This is derived infrastructure for Conrad's
`HenselianExtensionPointEmbeddingStatement`, using the already constructed
coefficient-extension map and the separated-space embedding argument. No new
literature assertion is attributed to the source.

`ExtensionLocalReduction.coveredHenselianExtensionPointHomeomorphRange` constructs
the canonical homeomorphism from `X(K)` to the range of `extensionPointMap L X`
under the full geometric hypotheses of the target: `K,L : Type u` are
nontrivially normed fields, `L` is a normed `K`-algebra, both are henselian, `X`
is quasi-separated and locally of finite type over `K`, and
`IsCoveredBySeparatedOpenSubspaces K X` holds. The source and target carry their
respective etale-chart topologies; the range carries the subspace topology.
The extension has arbitrary degree and transcendence degree.

## Helpers and implemented argument

All declarations below are in the `ExtensionLocalReduction` namespace.

- `locallyOfFiniteType_of_open` shows that an actual open immersion of algebraic
  spaces inherits local finite type over any scheme base. Pull back an atlas of
  the ambient space: its projection to that atlas is a scheme open immersion,
  while its projection to the open subspace is etale and surjective.
- `mem_range_of_changeRing_mem_range` says that a rational point lies in an open
  subspace if its extension to any field extension does. The range of the open
  immersion is a representable open subfunctor. Membership in it descends along
  the surjective map of the field spectra. No topology or henselianity is used.
- `extensionPointMap_natural` proves compatibility with actual base-change maps
  of spaces. `preimage_range_baseChangeMap` combines this with open membership
  descent to identify the inverse image of the extended open subspace's range.
  These two helpers assume a normed extension only because they use
  `extensionPointMap`; they require no henselianity.
- `separated_open_properties` supplies quasi-separated local finite type for a
  separated open subspace of `X`. Separatedness implies quasi-separatedness;
  local finite type follows by the preceding atlas construction.
- `preimage_range_extensionPointMap` identifies the preimage, under the extended
  open-subspace point map, of the ambient extended rational locus with the open
  subspace's own extended rational locus. It assumes `X` quasi-separated and
  locally of finite type, the subspace separated, and the target field `L`
  henselian; the open embedding on `L`-points is injective.
- `isEmbedding_of_covered` proves the embedding with the full separated-open
  covering hypothesis. At each rational point choose a separated open subspace
  containing it. Its coefficient-extension map is an embedding by
  `isEmbedding_henselianExtensionPointMap`. Its open embeddings into the ambient
  point spaces and the inverse-image identity give ambient neighborhoods that
  recover every source open set. The same identities and separated-subspace
  injectivity prove global injectivity. The displayed range homeomorphism is
  then `IsEmbedding.toHomeomorph` for this map.
- `isClosed_range_of_separated_open` reduces closedness to the separated open
  subspaces: for every separated open immersion `U → X`, assume the image of
  `U(K) → U_L(L)` is closed. For any target point outside the ambient rational
  locus, the covering hypothesis supplies such a subspace containing that
  `L`-point. Its complement to the closed rational locus maps to an open ambient
  neighborhood disjoint from the ambient rational locus. This helper assumes
  henselianity of `L`, but not of `K`.

## Remaining obligation

This module proves the entire embedding part and gives a localization reduction
for closedness. It does not prove closedness of the separated-space rational
locus under the assumption that `K` is closed in `L`, and so does not prove the
whole `HenselianExtensionPointEmbeddingStatement`.
