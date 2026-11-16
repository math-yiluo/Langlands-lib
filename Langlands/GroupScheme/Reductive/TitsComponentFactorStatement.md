# Actual factors realizing absolute Cartan components

This is an internal structural prerequisite for transferring results about
absolutely almost-simple groups to the connected Cartan components of a
semisimple group. The module defines the required witness and states its
existence. It does not prove the existence statement.

For an actual Tits index `d` and a simple vertex `a`,
`TitsIndexData.ComponentFactor d a` records:

- A finite separable extension `E/k`, at the same universe parameter.
- An actual affine group scheme `H/E` of locally finite type which is simply
  connected and absolutely almost-simple.
- A simply connected group scheme `N/k` and an actual central isogeny
  `Res_(E/k)(H) × N → G`. The source of this isogeny is also required to be simply
  connected. Thus the realizing group is a factor of an actual simply connected
  central cover; it is not merely an abstract matrix with the right shape.
- Actual Tits-index data `e` for `H`, and an equivalence from all its simple
  vertices to the actual connected Cartan component of `a`. Under this
  equivalence every integral Cartan entry of `e` equals the corresponding entry
  of `d`.
- A comparison of the full star images. Every absolute Galois element of `k`
  that takes `a` into its Cartan component is represented on that entire component
  by one absolute Galois element of `E`. Conversely, each absolute Galois element
  of `E` is represented on the component by one absolute Galois element of `k`.
  The existential Galois element is outside the vertex quantifier in both
  directions. These are comparisons of the complete induced permutation
  images, without choosing an identification of separable closures.
- The implication that if `G` is anisotropic, then `H` is anisotropic.

The comparison does not assert that the absolute Galois action fixes the
component: elements taking it to another component are allowed. The first
star-image comparison applies precisely to its stabilizer. The second has its
image inside that stabilizer: take the preimage of `a` under the vertex
equivalence, and use symmetry and transitivity of `CartanConnected`.

`SemisimpleTitsComponentFactorStatement` asserts that this witness exists for
every actual Tits index and each of its simple vertices over an arbitrary field.
Semisimplicity is already a field of `TitsIndexData`. If the diagram is empty,
the universal quantification over its vertices is vacuous.

The provenance is internal: the witness isolates the missing compatibility
between the published simply connected central-cover, finite product and
almost-simple Weil-restriction constructions and the published actual Cartan
and star-action interfaces. Those separate constructions alone do not establish
the Cartan and full-star comparisons required here. No proof of this new
statement, local anisotropic type-A theorem, or local rank-one enumeration is
claimed.
