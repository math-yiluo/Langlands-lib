# The inverse coordinates of the represented dynamic multiplication isomorphism

Let `G` be a separated group scheme over any scheme `S`, with an actual
cocharacter `χ : G_m → G`. Suppose its dynamic subgroup functors `P(χ)`,
`Z(χ)` and `U(χ)` are represented by `iP : P → G`, `iZ : Z → G`
and `iU : U → G`. These are the same explicit hypotheses as in
[`SchemeDecomposition`](SchemeDecomposition.md).

This module identifies the coordinates of that module's actual multiplication
isomorphism `m : U ×_S Z ≅ P`:

- `multiplication_comp_limitGroupHom` proves `m.hom ≫ limitGroupHom = pr₂`.
- `multiplicationIso_inv_snd` proves `m.inv ≫ pr₂ = limitGroupHom`.
- `multiplicationIso_inv_fst_comp` proves that the unipotent coordinate of
  `m.inv`, followed by `iU`, equals `iP · (limitGroupHom ≫ iZ)⁻¹`.

All declarations are in `Langlands.GroupScheme.Dynamic`. The equations are
equalities of morphisms in `Over S`, so they hold after restriction to every
test scheme, including nonreduced tests. The first two retain the actual
representing centralizer as target, rather than only comparing its image in
`G`.

## Provenance and proof

This is an internal consequence of the already constructed
`multiplicationIso`, `limitGroupHom` and the proved point-level limit formula
`Dynamic.limit_mul`. It asserts no new result from the literature.

For the first equation, cancel the representing monomorphism `iZ`.
The defining equation of `limitGroupHom` and
`pointsEquiv_comp_multiplication` reduce the result to
`limit_mul`: the limit of `u z` is `z`.
Precomposition with the inverse of the multiplication isomorphism gives the
second equation. For the third, precompose the ambient multiplication
equation with that inverse. Substitute the second equation and rearrange
`p = u z` in the group of morphisms to `G`, obtaining `u = p z⁻¹`.

The hypotheses do not include affineness, smoothness, finite presentation or
reductivity. Representability and separatedness remain hypotheses here.
The first-coordinate formula is an equation of scheme maps and makes no claim
that the first coordinate is a homomorphism for the direct product group law.
