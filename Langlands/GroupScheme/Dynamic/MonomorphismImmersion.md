# Immersions from closed dynamic centralizer restrictions

This is an internal consequence of the actual cartesian dynamic triple-cell
square, closedness of its factor map when the centralizer restriction is
closed, and the geometric identity-neighbourhood immersion criterion. It
asserts no separate translation from external literature.

For any three group schemes `M`, `Z`, `U` over a scheme `S`,
`tripleCellIdentity M Z U` is the morphism from the monoidal unit of `Over S`
to `M × (Z × U)` obtained by pairing their identity sections.
For arbitrary group homomorphisms from these factors into `G`,
`tripleCellIdentity_comp` says that this tuple followed by
`tripleCellMultiplication` is the identity section of `G`. The proof uses
preservation of the identity by each homomorphism and multiplication of
three identity sections.

Let `H` and `G` be smooth affine group schemes over an arbitrary scheme `S`,
with `H` having geometrically connected fibres, and let `f : H ⟶ G` be
monic in `Over S`. Supply a cocharacter `χ : Gm S ⟶ H` and representatives
of the three actual dynamic functors `U_H(-χ)`, `Z_H(χ)`, `U_H(χ)` and of
the corresponding three functors in `G` for `χ ≫ f`.

The theorem `isImmersion_of_isClosedSubgroup_centralizer` assumes that
the induced restriction from the supplied representative of `Z_H(χ)` to
that of `Z_G(χ ≫ f)` is a closed immersion. It concludes that the
underlying scheme morphism of `f` is an immersion.

The target triple-cell multiplication is open. The actual triple-cell
factor map is closed by `isClosedImmersion_tripleCellFactor`, whose two
unipotent restrictions are closed by the arbitrary-base unipotent
monomorphism theorem. The cartesian square
`isPullback_tripleCellFactor` is reflected from schemes to `Over S` and
flipped to put source multiplication and the factor map on its top and
left sides. The identity tuple in the target cell supplies its identity
section lift. These data satisfy
`IdentityCell.isImmersion_of_isPullback`, which gives the claimed immersion
on all of `H`.

The result holds in every universe and over arbitrary base schemes.
The centralizer closedness assumption remains explicit. The conclusion
is the ordinary locally closed immersion of schemes; this module does not
prove global closedness of `f` or the reductive closed-immersion theorem
`ReductiveMonomorphismClosedImmersionStatement` (in
`Langlands.GroupScheme.Reductive.MonomorphismClosedImmersionStatement`).
