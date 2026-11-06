# Actual central complements of compatible derived tori

This internal construction starts with an actual connected reductive group `G`
over a field, its actual derived subgroup `d : D ⟶ G`, maximal split tori
`j : T ⟶ D` and `i : S ⟶ G`, and an actual map `e : T ⟶ S` satisfying
`j ≫ d = groupHom e ≫ i`. An actual integral root datum for `i` is supplied.

`DerivedTorusCentralComplement e i` records an actual split torus `A`, an actual
map `c : A ⟶ S` with central composite into `G`, and flatness and scheme
surjectivity of the product of `e` and `c`. The construction proves this type
inhabited and chooses an inhabitant.

Choose the largest central split torus of `G` using `splitComponentStatement`.
Its map factors through the maximal split torus `S` because it commutes with it.
The supplied actual root datum gives actual normalizing reflection points, and
the integral Weyl sum annihilates every root. Root-annihilator centrality makes
the actual Weyl norm central. The published derived-valued Weyl complement and
central Weyl norm then factor a nonzero power map through the product, proving
scheme surjectivity. Flatness follows from the general flatness theorem for a
surjective homomorphism from a group of finite type to a smooth group; here both
factors are split tori.

The provenance is internal: all geometry and reflection arguments are supplied
by existing proved interfaces and the explicitly supplied actual root datum.
This module does not prove existence of actual root data, reductivity of a
centralizer, or the full derived split-torus-centralizer coroot comparison.
