# Positivity of proportional polarizations

`polarizationRayPositivity` proves `PolarizationRayPositivityStatement`
in its stated universe and characteristic range. It compares two actual
polarizations into the same constructed dual on a nonempty base, in
positive relative dimension.

`DualWitness.poincareDiagonalClassHom` sends a homomorphism \(\lambda\)
to the line-bundle class of its diagonal Poincaré pullback
\((1,\lambda)^*\mathcal P\). The identity and product formulas
follow by evaluating the Poincaré class at the identity morphism of the
abelian scheme, using the published multiplicativity in the dual variable.
Here the additive group of homomorphisms is written multiplicatively so
that it maps to line-bundle classes under tensor product.

The proof of positivity chooses an algebraic closure of the residue field
of a point of the base. The polarization condition supplies a field-ample
Mumford presentation there. `poincareDiagonal_isAmple_of_fieldPresentation`
and the diagonal base-change isomorphism make each pulled-back
diagonal bundle ample on the same geometric fibre.

If the two proportionality coefficients have nonpositive product, their
equation gives a sum of nonnegative integer multiples of the two
homomorphisms equal to zero, with the coefficient of the second
polarization positive. Multiplicativity of the diagonal class and its
pullback make the tensor product of the corresponding powers trivial.
The product is ample by the positive-power and tensor-product results,
with the zero-exponent case using the right unit isomorphism. A proper
scheme over a field with an ample trivial bundle is finite over that
field, by `properAmpleTrivialFinite`. The abelian scheme on the geometric
fibre has a unit point. At that point, its finite structure morphism gives
relative dimension zero and its specified smooth relative dimension gives
the positive integer in the statement. The contradiction gives positivity.

This argument uses the Library's diagonal Poincaré class and relative
polarization predicates. The proportionality equation is the
characteristic-zero scalar convention in Harris–Taylor, *The Geometry
and Cohomology of Some Simple Shimura Varieties*, III.1, printed p. 91
(PDF p. 99). The proof above establishes the sign using actual geometric
polarizations in the broader scope of the published proposition.

Source for the scalar convention
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`,
III.1, printed p. 91 (PDF p. 99).
