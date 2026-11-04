# Affine-line constancy from anisotropic polynomial relations

Author: Worker 1478.

This derived module translates the polynomial constancy result in
`Unipotent.PrincipalPart` into constancy of actual scheme morphisms.
Its source motivation is the highest-degree argument in
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Definition B.1.6 and Lemma B.1.7, printed pp.563–564, one-based PDF
pp.589–590. The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

The field is arbitrary, in universe `u`. Given actual group schemes `G`
and `V`, natural vector coordinates `e` of dimension `n` on `V`, and a
relative scheme morphism `j : G.X ⟶ V.X`,
`HasSeparatedPolynomialRelation j e f` asserts the single global-function
equation
`∑ i, (f i).eval₂ (structureMap G.X) ((e G.X j).toAdd i) = 0`.
The equation is on the universal point of `G`. The lemma `eval_eq_zero`
pulls it back to every relative scheme using naturality of the
coordinates and compatibility of the ground-field structure maps.

The auxiliary theorem
`exists_scalar_coordinates_of_anisotropic_relation` concerns functions on
the actual affine line over `k`. Assuming that all `f i` have zero
constant coefficient and that their principal part is anisotropic over
`k`, every tuple satisfying the equation consists of scalar functions.
The proof uses the published identification of global functions on the
affine line with `k[X]`, chooses polynomial representatives, and uses its
injectivity to obtain a zero sum of polynomial compositions. The
principal-part constancy theorem identifies the representatives with
their constant coefficients.

The main theorem
`hasConstantAffineLineMaps_of_anisotropic_relation` assumes in addition
that `j` is a categorical monomorphism. For any actual affine-line map
`a` into `G`, the pulled-back equation makes every vector coordinate of
`a ≫ j` a scalar. Pullback along the endomorphism of the affine line
that factors through its zero section preserves these scalars.
Coordinate injectivity and cancellation of `j` therefore show that `a`
is the constant map with value its restriction to the zero section.
This is the exact existing predicate `HasConstantAffineLineMaps G`.

No group homomorphism property of `j`, affine presentation of `G`,
smoothness, connectedness, unipotence, field infinitude or
characteristic restriction is assumed. All scheme morphisms and
coordinate naturality use the existing relative-scheme interfaces.
The provenance is derived: CGP's polynomial argument together with the
affine-line coordinate-ring identification and cancellation of a monic
coordinate map gives the stated result over every field.

This theorem requires the supplied monic vector-coordinate map and
anisotropic relation. It does not construct such presentations for
arbitrary unipotent groups, prove the converse woundness criterion,
extract central additive subgroups, or prove the host rational-lifting
statement.
