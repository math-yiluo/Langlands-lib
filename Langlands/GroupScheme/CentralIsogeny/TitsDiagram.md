# Actual Cartan and full star diagrams under central isogenies

This derived internal construction compares the full absolute Cartan diagram
and full star action of actual semisimple groups under a central isogeny.
It does not require their full character lattices to be isomorphic.

A source maximal torus maps to its actual closed schematic image. The source
map is finite, so its schematically dominant map to that image is surjective;
the published central-isogeny image theorem makes the image a maximal torus.
Over the separable closure, construct actual target root data and a base.
The published central-isogeny root morphism gives the root-index bijection
and injective weight and coweight maps. Transport the target base to the source
root datum with `RootDatumHomBase.mapBase`, and choose the corresponding root
pinning. Character pullback is Galois equivariant, so `StarActionHom` proves
full star naturality on every root.

`GaloisPinningData.CentralImage` retains the target pinning, compatible source
base and root pinning, actual root-datum morphism, both lattice injections,
base correspondence and ordinary character-action intertwining. Its `source`,
`basedHom` and `star_eq` expose the resulting simultaneous full star comparison.
`centralImage` chooses these data for the actual central isogeny and a source
pinning whose original torus is maximal.

`TitsIndexData.CartanStarEquiv` records an equivalence of every simple vertex,
every ordered integral Cartan entry and every full absolute-Galois star
permutation. This comparison deliberately contains no assertion about zero
restrictions to maximal split tori.

`nonempty_cartanStarEquiv_of_centralIsogeny` and
`cartanStarEquivOfCentralIsogeny` supply this entire comparison for any actual
Tits-index choices on the source and target of a central isogeny. The proof
uses the compatible central-image pinnings and the published same-group star
independence theorem at each end. It composes those vertex equivalences with
the inverse of the actual central-isogeny root-index bijection. Pairing
preservation gives every ordered Cartan entry, and the three simultaneous
star-intertwining laws give the comparison for each absolute Galois element.
The field, characteristic and universe are unrestricted.
