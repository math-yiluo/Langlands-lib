# Reductivity ascent for affine groups with torus kernel

`Langlands.GroupScheme.TorusKernelReductiveAscentStatement` states the
following internal helper over every field, including imperfect fields.
Let `E`, `G` and `T` be group schemes over the field, with `E` affine.
Let `i : T ⟶ E` be a closed subgroup inclusion with `T` a torus, and let
`p : E ⟶ G` be an actual fppf quotient by the full range of `i`.
If `G` is connected reductive, then `E` is connected reductive.

The quotient predicate requires flatness, scheme surjectivity, local finite
presentation and equality of the entire kernel range with the range of `i`
on every relative scheme test. The statement assumes affineness of the source
explicitly. It does not assume that the source is smooth or connected, and it
does not require the torus kernel to be central.

This is a derived internal prerequisite for Task 6660's common domination of
actual z-extensions. In the fiber-product construction the source is already
affine, and its projection to one supplied extension has torus kernel.
The helper isolates the needed reductivity conclusion without adding it as
an assumption to the final common-domination proposition. It uses the existing
Library meanings of torus, represented fppf quotient and connected reductivity;
it is not presented as a separately quoted statement from the literature.
