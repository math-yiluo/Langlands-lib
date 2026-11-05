# Closed generation and homomorphism uniqueness from the dynamic triple cell

This derived support module concerns actual group schemes over `Spec k`, for
an arbitrary field `k : Type u`. Suppose that `G` is smooth, affine, and
connected, and let `χ : Gm → G` be any cocharacter. Write `−χ` for
precomposition with `Gm.powerHom (-1)`.

The factors are the intrinsic functors `U(−χ)`, `Z(χ)`, and `U(χ)`.
In the represented versions of the results, `iM`, `iZ`, and `iU` represent
these functors on every scheme over the base. Their multiplication is the
published actual scheme morphism

`tripleCellMultiplication iM iZ iU : M.X × (Z.X × U.X) → G.X`.

The module proves the following consequences.

- `isDominant_tripleCellMultiplication` and
  `isSchemeTheoreticallyDominant_tripleCellMultiplication` show that this
  morphism is dominant and scheme-theoretically dominant.
- `isIso_of_contains_tripleCell` says that a closed subgroup `d : D → G`
  containing the range functors of all three inclusions is an isomorphism of
  group schemes. No smoothness, reducedness, or connectedness assumption on
  `D` is required.
- `hom_ext_of_tripleCell` says that homomorphisms `f,g : G → H`, for any group
  scheme `H` separated over `k`, are equal if `iM ≫ f = iM ≫ g`,
  `iZ ≫ f = iZ ≫ g`, and `iU ≫ f = iU ≫ g`.
- `isIso_of_contains_dynamicFactors` removes the choices of representatives
  from the closed-generation statement. Its hypotheses are precisely that
  `d` is a closed subgroup and that `U(−χ)`, `Z(χ)`, and `U(χ)` are each
  contained in its range functor. The proof constructs their canonical affine
  representatives internally.
- `isoOfContainsDynamicFactors` packages this result as an actual isomorphism
  `D ≅ G` of group schemes. Its forward map is the given inclusion `d`, as
  recorded by `isoOfContainsDynamicFactors_hom`; its inverse is the categorical
  inverse obtained from the proved `IsIso d` instance.

For density, the source contains the product of the identity points over
`Spec k`. The published `smoothConnectedAffineGeometry` theorem makes `G`
geometrically integral, hence integral. The published triple-cell open
immersion therefore has a nonempty open image in an irreducible space, which
is dense. Reducedness of `G` upgrades dominance to scheme-theoretic dominance.

For closed generation, the helper `tripleCellMultiplication_mem` uses the
three projection maps and closure under multiplication to show that the
universal cell product belongs to the range functor of `d`. Thus it factors
through `D` as a morphism of schemes over the base. Dominance of the cell
implies dominance of `d`. Its image is also closed, so `d` is surjective on
underlying points. A surjective closed immersion into the reduced scheme `G`
is an isomorphism; the forgetful functors then reflect this to an
isomorphism of group schemes. This is closed generation, with no assertion
that products of points from the factors exhaust `G(T)` on each test scheme.

For homomorphism uniqueness, the general-base helper
`tripleCellMultiplication_comp_hom` expresses preservation of multiplication.
The three restriction equalities make `f` and `g` agree after the cell
morphism. Mathlib's extensionality theorem for a reduced source, a separated
target over the base, and a dominant test morphism gives equality everywhere.

No external literature is newly cited: these are derived consequences of
`Absolute.TripleCell`, `SmoothConnectedGeometryProof`, intrinsic affine
representability, and Mathlib's density and separatedness criteria. The field
may be imperfect and have positive characteristic; no reductivity or
splitting hypothesis is used. The module does not identify `Z(χ)` with a
chosen maximal torus, construct root-group parametrizations, or prove the
common-torus split-isomorphism theorem.
