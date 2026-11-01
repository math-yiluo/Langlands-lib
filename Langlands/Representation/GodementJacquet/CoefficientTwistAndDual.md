# Actual bi-smooth coefficients under twists and inverse transpose

This derived algebraic prerequisite supplies the actual coefficient-image
transports needed for the matched adjacent-rank rational products. Its
scalar function formulas are those used on printed p.437 of JPSS
Section 6.3:
`(f tensor chi)^iota = f^iota tensor chi^-1`. It also proves membership in
the actual bi-smooth coefficient spaces of the constructed twisted and
pullback coefficient models.

`coefficientTwist chi` is the linear multiplier
`f(g) -> chi(g)*f(g)` on actual scalar group functions.
`map_biSmoothMatrixCoefficients_twist_le` proves that, for a character
with open kernel, this multiplier carries the entire actual bi-smooth
coefficient submodule into that of the twisted action. On each spanning
coefficient, use the same original vector and algebraic functional.
The published smooth-vector twist theorem preserves their smoothness;
the published dual-twist identity gives the inverse character on the
dual action. Linearity of the multiplier then gives the inclusion on
the whole coefficient span. `biSmoothCoefficientTwist` packages the
result as an actual coefficient subtype with exactly that function.
The original representation needs no smoothness, admissibility or
irreducibility hypothesis.

`coefficientModelCharacterEquiv` transports the actual right-translation
model representation along equality of its covariance characters and
the corresponding transported functional. Its proof eliminates the
character equality and uses the identity representation equivalence.
It asserts an equivalence between these two actual coefficient images,
not between an original carrier and its image.

For standard Whittaker character `psi`, a specified functional `ell`,
and any actual bi-smooth matrix coefficient `f` of its coefficient-image
right-translation representation,
`determinantTwistModelCoefficient` is an actual bi-smooth coefficient of
the coefficient image of the determinant-twisted original
representation. Its unchanged scalar function is
`g -> chi(det g)*f(g)`. The proof first applies the coefficient-twist
inclusion, then the published actual determinant-twist model equivalence.
The open-kernel hypothesis on the units character pulls back through the
actual continuous determinant map.

`iotaModelCoefficient` constructs the scalar function
`coefficientIota f = f composed with inverseTranspose` as an actual
coefficient of the inverse-transpose pullback's specified dual
coefficient image. The proof uses the existing continuous group
pullback inclusion for all actual bi-smooth coefficients and the actual
dual model equivalence. `iotaScaledModelCoefficient` transports this
same coefficient image to the standard character for `psi.scale(-1)`
by the character equality and the coefficient-model representation
equivalence proved here.

`coefficientIota_determinantTwist` proves the exact equality of whole
scalar functions

```text
coefficientIota(chi(det)*f)
  = chi^-1(det) * coefficientIota(f).
```

Its proof uses the actual determinant of inverse transpose, which is
the inverse determinant, and the character homomorphism's inversion
law. `iotaDeterminantTwistModelCoefficient` combines the original twist
and constructed dual coefficient transports. It is an actual
bi-smooth coefficient of the standard-character coefficient image of
the inverse-transpose pullback of the determinant-twisted original
representation. Its evaluation theorem is exactly the displayed
inverse-character function, with no replacement of the original `f`.

The field and original carrier have independent universes. The
constructions retain every natural rank, including actual rank one;
zero functionals and reducible representations are allowed. No
topology is imposed on representation carriers. No smooth
contragredient identification or original-carrier/model equivalence is
assumed. The generic coefficient twist accepts an open-kernel character;
these are transport hypotheses and not new premises of either
adjacent-rank parent statement.

The registered source is Jacquet–Piatetski-Shapiro–Shalika,
*Rankin–Selberg Convolutions* (1983), `jpss-1983-rankin-selberg`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.404–405 and 427–439 were read in preceding work, and p.437
was visually reread for the actual transformed finite family and
twisted coefficient identity. The coefficient-span and
character-congruence transport proofs are internal algebraic
formalization of those literal function identities. The earlier bounded
registered-source and correction-note audit found no JPSS-specific
registered erratum.

This module constructs the exact actual coefficient data. Matrix
convergence, rational-value existence, functional equations, reflection
sign comparison, model realization, and both parent gamma/L results
remain separate.
