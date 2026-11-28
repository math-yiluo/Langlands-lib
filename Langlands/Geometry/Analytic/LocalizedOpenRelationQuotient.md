# The pieces are open subspaces of the glued space

For gluing data `R : LocalizedOpenRelation K`, this module constructs the morphisms
from the pieces to the glued space `glued R` (module
`LocalizedOpenRelationPresentation`) and shows that they are open immersions.
Namespace: `Langlands.Analytic.SaturatedAtlasPresentation.LocalizedOpenRelation`.

## Construction

- `pieceRange m` is the image of `ι m` and `pieceDomain m` the corresponding open
  analytic domain of the glued presentation.
- `pieceMap m : presentationOf (Z m) ⟶ (presentation R).domain (pieceDomain m)` is
  the strong map with base map `z ↦ ι m z` and pullback `rho ⟨m, i⟩ (rep c)` for a
  chart `i` of the piece and a chart `c` of the open domain containing its image
  (`pieceChart_image_subset`). The chart identity is `rho_chart`; compatibility with
  restrictions is `rho_unique`, `cmap_rho`, `cmap_restriction` (from
  `SmallAffinoidSpectrum.chartMap_of_subset`) and `rho_comp`.

## Results

- `isQuasiIso_pieceMap`: `pieceMap m` is a quasi-isomorphism. Its base map is the
  homeomorphism of `Z m` onto the image of the open embedding `ι m`. Each pullback
  represents its image locus: the locus is closed and is the range of the pullback
  by the general strong-map facts `isClosed_chartImageLocus` and `range_pullback`,
  and the factorization property is `rho_universal`.
- `pieceIso m` is the resulting isomorphism of `Z m` with the open domain, and
  `ιL m` is `pieceIso m` followed by the inclusion of the domain.
- `openImmersion_ιL`: `ιL m` is an open immersion, by the definition of
  `openImmersion`.
- `ιL_apply`: on points, `ιL m` is `ι m`.

## Provenance

Derived. Property (1) of the glued space in Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), §1.3, printed p.24 / PDF p.21
(`berkovich-1993-etale-cohomology`): each piece is isomorphic to an analytic domain
of the glued space, open in case a) of Proposition 1.3.3. The isomorphism is
obtained from the Library's localization at quasi-isomorphisms.
