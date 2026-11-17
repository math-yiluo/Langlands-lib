# Torus compatibility of coordinate cell isomorphisms

This internal support module derives two compatibility facts from the published
integral-coordinate torus and coordinate-cell constructions. It does not assume
or prove the affine split Isomorphism Theorem.

`LocalSplitCell.cellTorusSection R I m n` is the canonical morphism from the
coordinate torus to the coordinate cell with zero negative and positive root
coordinates. It is constructed using the existing inverse coordinate map
`mkCellPoint`. Composing this section with any cell map recovers its supplied
torus embedding, as proved by `cellTorusSection_comp_cellMap`.

`splitTorus.pointsEquiv_exponentEquivGroupIso` evaluates the torus isomorphism
associated with an integral linear equivalence `e : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ)` on
every test scheme. Pullback of the character with exponent `m` has exponent
`e.symm m`. The proof evaluates the existing equality
`exponentHom_comp_exponentCharacter` using
`pointsEquiv_exponentCharacter`; hence it works over an arbitrary base scheme.

`LocalSplitCell.mkCellPoint_zero_comp_cellMap` identifies the coordinate cell map
on a point with zero negative and positive root coordinates with the given torus
embedding. It substitutes the published coordinate formulas and uses that each
ordered product at zero is the identity.

`LocalSplitCell.torus_comp_of_cellMap_comp` restricts an equality of coordinate
cell maps under a group morphism `ψ` to those zero-root points. Applying it to the
identity point of the coordinate torus proves `i ≫ ψ = i'`. This argument works
over every commutative ring and uses no geometric hypotheses on the groups.
