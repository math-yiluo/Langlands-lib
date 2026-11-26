# Euler comparison for spherical pairs and norm twists

`SphericalPairNormTwistEulerStatement.{u,v}` takes a finite relative extension
of bundled p-adic fields, with residue degree `f`, and two spherical actions in
positive ranks on each field. Each upper Satake multiset is the `f`-th power of
the corresponding lower multiset. Fix a lower quasicharacter `μ`. The first
upper action is twisted by `μ` composed with the field norm. The first lower
action is twisted by `κ * μ`, one twist for each character `κ` trivial on the
norm. The `IsAutomorphicPairLPolynomial` hypotheses certify the polynomials of
those actual twisted classes paired with the corresponding second actions.
The identity expresses the product of the lower polynomials as the upper
polynomial with its variable replaced by `X ^ f`.

`sphericalPairNormTwistEuler` uses `sphericalPairTwistLPolynomial` to write each
pair denominator as a product of Tate denominators over ordered pairs of
Satake entries. Multiplication by an unramified Satake character preserves
the conductor of the twist. At conductor zero, each linear factor uses the
product of the two entries and the twist's uniformizer value. At positive
conductor each Tate polynomial is one.

The proof presents both Satake multisets as tuples and commutes the products
so that each pair of entries has its own norm-character product. The relative
norm multiplies normalized order by `f`, so pulling back the unramified
character of the product of two entries gives the unramified character of their
`f`-th powers. The existing theorem `prod_lPolynomial_normTwists` compares the
Tate polynomials of each such pair. Polynomial substitution preserves
products, which gives the stated comparison with all multiplicities.

The provenance is the blockwise argument of Henniart–Lemaire, *Changement
de base et induction automorphe pour GLₙ en caractéristique non nulle* (2011),
II.6.11, printed pp. 127–128 (PDF pp. 135–136). Their spherical calculation
uses the pairs of inducing characters and a product over norm characters.
The retained source ID is
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`
and its SHA-256 is `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
Trace Formula* (1989), Chapter 1, §6.4, equation (6.8), printed p. 61 (PDF
p. 75), records the unramified case. The retained source ID is
`arthur-clozel-1989-base-change` and its SHA-256 is
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
The use of the full abelian norm comparison allows an arbitrary auxiliary
quasicharacter and any finite relative field extension under the supplied
spectral hypotheses.
