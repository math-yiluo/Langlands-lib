# Open maps for coordinate point topologies

Author: Worker 109.

This is an internal construction and a topological reduction for the proof of
Conrad's Theorem 5.9. It uses the published `coordinatePointMap`,
`coordinatePointTopology`, `coordinateProductTopology` and
`CoordinatePointTopologyFacts.isHomeomorph_coordinatePointMap`.
It does not assert that a smooth morphism satisfies the local hypotheses.

For a commutative base ring `C`, a `C`-algebra `A`, families of commutative
`C`-algebras `R i` and topological fields `L i`, and algebra maps
`π i : A →ₐ[C] R i` and `φ i : R i →ₐ[C] L i`,
`coordinatePointHomeomorph` packages a bijective coordinate point map as an
explicit homeomorphism. The source has its defining coordinate topology; the
target has the product of the factor topologies induced from the étale-chart
topologies of the base changes to `L i`. No continuity hypothesis on the
coefficient maps is needed for this construction.

`coordinatePointMap_map` is the naturality identity for a morphism of algebraic
spaces and change of coefficients. `isOpenMap_coordinatePointMap_of_local`
assumes both coordinate maps are bijective, each factor point map is open, and
the factor maps are surjective at all but finitely many indices. Mathlib's
`IsOpenMap.piMap` gives openness on the product. Naturality identifies the
original point map with this product map through the two coordinate
homeomorphisms, so the original point map is open.

The source and target are arbitrary algebraic spaces over `Spec C`; the index
type is arbitrary and may be empty. The coefficient rings need not be local.
For the intended adelic application, Proposition 5.2 provides the required
coordinate bijections for separated spaces of finite type.

The provenance is derived: these constructions and lemmas concern the actual
published coordinate topologies and follow formally from their definitions and
Mathlib's product theorem for open maps. They do not prove Conrad's
unconditional Theorem 5.9 or a Lang–Weil estimate.
