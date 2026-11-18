# Inverses of actual local quasi-isogenies

`Langlands.FormalGroup.ModuleLaw.localQuasiIsogenyInverse` proves
the published proposition
`Langlands.FormalGroup.ModuleLaw.LocalQuasiIsogenyInverseStatement`
with its existing hypotheses, over arbitrary commutative coefficient
rings O, commutative O-algebras R, O-algebra fields F in the universe
of R, distinguished scalars and finite coordinate types.

For each input local quasi-isogeny and each point of its open set,
choose a neighbourhood on which a scalar power times its actual
forward section is the integral image of an actual isogeny.
Coefficient extension retains scalar divisibility on the genuine
ring of sections of that neighbourhood.

The integral-dual theorem gives actual reverse integral isogenies
at all sufficiently large scalar-power exponents. Its proof uses a
common scalar annihilator of the universal represented kernel point,
factorization by faithfully flat descent of actual points, and
reconstruction of a formal power-series homomorphism from its values
on truncated polynomial test algebras. The finite-kernel proof uses a
finitely presented quotient of the scalar-kernel algebra, an actual
torsor translation pushout and faithful-flat descent of flatness,
then finite presentation to establish projectivity.

Choose a dual exponent at least as large as the local denominator
exponent. Multiplication of its integral image by the inverse of the
remaining scalar power gives an actual reverse rational Hom section.
Bilinearity proves both actual section inverse equations. Multiplying
the reverse section by the remaining scalar power recovers its actual
integral isogeny numerator, proving the reverse local scalar-isogeny
condition.

On overlaps these local inverses agree because their forward sections
are the restrictions of the same actual section. The actual rational
Hom sheaf therefore glues them, and locality retains the reverse
scalar-isogeny condition. Equality from the prescribed forward section
proves uniqueness of the resulting actual section isomorphism.

The construction permits point-dependent neighbourhoods and
denominator exponents. It uses the nonzero scalar image and actual
scalar-divisibility hypotheses already retained by the input. It
adds no domain, fraction-field, discrete valuation or uniform
denominator hypothesis. This proof follows the internal integral
numerator and gluing route described in the published target's
Markdown and is not presented as a quotation of external literature.
