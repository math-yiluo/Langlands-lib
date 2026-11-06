# Natural homomorphisms into an arbitrary affine group scheme

Author: Worker 112.

The published `Corepresented.groupSchemeMap` and `SplitComponent.natOfHom`
exchange natural homomorphisms of corepresented group functors with
homomorphisms of the corresponding affine group schemes. This file extends that
exchange to an arbitrary affine target. It also records the unit coordinates of
the lattice model of a split torus, and it shows that a split component absorbs
central homomorphisms from split tori that are not assumed to be closed
immersions.

## Arbitrary affine targets

Let `G` be an affine group scheme over `Spec R`. Let `F` be a group functor on
`R`-algebras, corepresented by `e`.

- `coordinatePointsEquiv G S` is a multiplicative equivalence from the
  `G`-points over `S` to the points of the published coordinate model
  `AffineCoordinates.functor G`. It is composition with the inverse of
  `AffineCoordinates.groupSchemeIso G`, followed by
  `Corepresented.affinePointsEquiv`. `coordinatePointsEquiv_naturality` and
  `coordinatePointsTrans` record its naturality.
- `homOfNat G e β` turns a natural homomorphism `β : F ⟶ G.affinePointFunctor`
  into a homomorphism of group schemes from `Corepresented.groupScheme F e` to
  `G`. `homOfNat_affinePoints` shows that it acts on algebra points by `β`.
  `isCentral_homOfNat` shows that it is central when `β` is central.
- `natToPoints e h` turns a homomorphism
  `h : Corepresented.groupScheme F e ⟶ G` into the natural homomorphism
  `χ ↦ (point of χ) ≫ h` (`natToPoints_app`). `isCentralNat_natToPoints` shows
  that it is central when `h` is central. This direction needs no affineness of
  `G`.

## Coordinates of the lattice torus

`algebraPointsEquiv_torusIso` concerns the published isomorphism
`torusIso R I` from the lattice torus of `FreeAbelianGroup I` to
`splitTorus (Spec R) I`. On points over an `R`-algebra `A`, the unit coordinates
of the image are the values of the character on the basis vectors, as given by
the published `freeCharEquiv`. The proof combines the point-model property of
`isoOfPointModels`, the published comparison
`Corepresented.map_affineSectionsIso_pointsEquiv`, and
`Scheme.ΓSpecIso`.

## Absorption by a split component

`IsSplitComponent.exists_comp_eq_of_isCentral` works over a field `k`, for an
affine `G` whose coordinate algebra is of finite type. Let `i` be a split
component of `G`, and let `φ : D ⟶ G` be a central homomorphism from a split
torus `D`. Then `φ` factors through `i`. Unlike the published
`IsSplitComponent.exists_comp_eq`, it does not require `φ` to be a closed
immersion. The proof uses the published universal property in
`exists_largestCentralSplitTorus` together with the maximality of `i`.

## Provenance and scope

This is an internal construction. It combines published Library results about
corepresented group schemes, the largest central split torus, and split tori. It
introduces no external mathematical claim.
