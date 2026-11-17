# Every character of a closed split torus occurs as a weight

`Langlands.GroupScheme.splitTorusCharacterWeight.{u}` proves the unchanged
published proposition
`Langlands.GroupScheme.SplitTorusCharacterWeightStatement.{u}` in every
universe. It applies to every affine group scheme over every field and
every closed split torus subgroup. There is no finite-type, smoothness,
connectedness or reductivity hypothesis on the ambient group.

The second conjunct gives the same conclusion for every character of the
maximal torus of a split pinning, using the target's
`representationWeightSpace`.

## Implemented proof

The argument uses the existing coordinate algebra
`CharacterUnits.Coord G`, its universal point, and actual morphisms of
group schemes as finite matrix representations.

1. `MatrixRepresentation.characterCoefficient_universalCharacterMatrix_eq_zero`
   treats a representation of a split torus. If its character space for
   `χ` is zero, its `characterProjector χ` vanishes on that space and on
   every other character space. The published split-torus decomposition
   `iSup_characterSpace_eq_top_of_isSplitTorus` and submodule induction
   show that the projector vanishes on every vector. Applying this to a
   standard coordinate vector shows that `characterCoefficient χ`
   vanishes on every entry of `universalCharacterMatrix`.
2. `SplitTorusCharacterWeight.exists_coefficients` puts a coordinate
   function `f` in the linear span of the coefficients of one finite
   matrix representation. It applies `Comodule.exists_matrix` to the
   singleton `{f}` and the coassociative, counital coordinate
   corepresentation. `Corepresented.LinearEmbedding.toGL` constructs the
   representation on its affine model, and
   `AffineCorepresentation.toModel` transports it to `G`. The lemma also
   proves, at every affine coefficient point `x`, that each actual matrix
   entry is `Lie.pointCoordinates G x` applied to the corresponding
   coordinate coefficient.
3. `SplitTorusCharacterWeight.restriction_surjective` treats any closed
   affine subgroup. The coordinate map is obtained by composing its
   universal point with the inclusion. Its spectrum map is the inclusion
   transported through the chosen coordinate isomorphisms, hence a closed
   immersion. Surjectivity of global sections for affine closed
   immersions and the naturality of `Scheme.ΓSpecIso` give surjectivity of
   this coordinate map.
4. `SplitTorusCharacterWeight.exists_character_weight` lifts the coordinate
   unit of `χ` through that surjection and applies `exists_coefficients`.
   If the restricted representation's `χ` space were zero, step 1 and the
   pointwise formula from step 2 would make the composite of coordinate
   restriction and `characterCoefficient χ` vanish on every coefficient.
   Its kernel therefore contains their span and the chosen lift. But its
   value on the lift is one, by `characterCoefficient_unit`. This gives
   the contradiction `1 = 0`.
5. `splitTorusCharacterWeight` supplies this result as the first conjunct
   of the exact target. For the second conjunct it uses `p.torus`,
   `p.inclusion`, `p.isSplitTorus`, and the closed-subgroup component
   `p.isMaximalTorus.2.1`, at the character corresponding to `lam`.

The finite-dimensionality input is the coalgebra theorem; its use does
not require finite generation of the coordinate algebra. The coordinate
and character arguments use universal affine points, so they apply over
arbitrary fields and retain the target's scheme-theoretic meaning.

## Provenance

This is an internal derivation of the published target. Its source
motivation is James S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`, Proposition 22.13 (printed pp. 465–466),
and Proposition 4.7 and Corollary 4.8 (printed p. 86). The source's
closed-subgroup coordinate lift, finite-dimensional comodule argument
and separation by characters motivate the proof. The implementation
uses matrix coefficients spanning the lift and character coefficient
functionals, rather than decomposing the whole regular representation
as in the printed proof. The generalization to arbitrary affine group
schemes is already part of the unchanged target and follows from these
coalgebra and affine-coordinate arguments.
