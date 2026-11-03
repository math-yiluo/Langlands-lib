# From natural homomorphisms to homomorphisms of group schemes

Author: Worker 1178.

This internal module transfers the functor-level results to the published
group schemes `Corepresented.groupScheme F e` over `Spec R`.

- `natOfHom e d φ`: a homomorphism `φ` of corepresented group schemes induces
  the natural homomorphism of algebra-point functors through
  `Corepresented.affinePointsEquiv`. It reuses `Corepresented.pointsTrans`;
  `groupSchemeMap_natOfHom` reuses `Corepresented.groupSchemeMap_pointsTrans`
  to show that `Corepresented.groupSchemeMap` of it is `φ`.
- `groupSchemeMap_comp`: `groupSchemeMap` respects composition, using the
  symmetric form of the published `Corepresented.groupSchemeMap_comp`.
- `isCentral_groupSchemeMap` and `isCentralNat_of_isCentral`: the published
  `IsCentral` of `groupSchemeMap e d α` (points over every test scheme commute
  with all points after every base change) follows from `IsCentralNat α`
  by the published `Corepresented.isCentral_groupSchemeMap`, and conversely
  implies it through affine points.
- `isClosedSubgroup_groupSchemeMap`: if the classifying map is surjective, the
  underlying scheme morphism, which is `Spec` of that map
  (`groupSchemeMap_hom`), is a closed immersion
  (`IsClosedImmersion.spec_of_surjective`).
- `freeCharEquiv` and `torusIso`: characters of `FreeAbelianGroup I` are
  `I`-families of units, naturally in the test scheme, so
  `isoOfPointModels` gives an isomorphism of group schemes between the
  lattice torus of `FreeAbelianGroup I` and the published
  `splitTorus (Spec R) I`.

## Provenance

Internal, on the published `Corepresented`, `isoOfPointModels`,
`splitTorus.pointsEquiv` and `IsCentral` interfaces.
