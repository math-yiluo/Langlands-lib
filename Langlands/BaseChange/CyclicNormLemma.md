# The cyclic norm lemma for `GL_n`

`Langlands.BaseChange.cyclicNormLemma` proves the Library proposition
`CyclicNormLemmaStatement.{u,v}`. The base field and cyclic algebra range over
independent universes. The theorem uses the Library's definitions of the norm,
association and the cyclic algebra hypothesis.

The proof first uses residue-field coordinates. The automorphism of a finite
reduced cyclic algebra permutes its maximal ideals in one cycle, since a
characteristic idempotent of any orbit is fixed and therefore belongs to the
base field. A chosen quotient gives all of the coordinates, with an induced
field automorphism at the wraparound. Evaluating the published norm in the
first coordinate groups its factors into blocks of the cycle length. The
partial products compare that norm with its other coordinates and transport
the twisted conjugator from the residue field to the full product.

For a cyclic field extension, the ordered invariant factors of the norm
product are fixed by the automorphism. The entrywise image is conjugate to the
original norm, and applying the automorphism to the factors gives a companion
form for the image. Uniqueness therefore puts the coefficients in the base
field. Their block companion matrix is invertible because its base change is
conjugate to the norm. This proves existence of a representative.

For uniqueness, expand the coefficients of a conjugator over the extension
in a basis over the base field. It gives an isomorphism of the same positive
number of copies of the two linear operators. For twisted conjugacy, conjugates
of a field basis give an invertible scalar matrix, by Dedekind independence.
Using that matrix and the successive transforms of a norm conjugator yields an
isomorphism of copies intertwining the two semilinear operators and scalar
multiplications. In both arguments, cancellation of copies of finite-dimensional
modules gives the required conjugator. These arguments apply over finite fields.

The entry theorem applies `cyclicNormLemma_of_field_exists` and discharges its
sole premise by `cyclicNormAssociated_of_field`.

## Sources

- Henniart and Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), §§I.2.1–I.2.2, printed pp. 10–12,
  PDF pp. 18–20. Source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
- Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
  the Trace Formula* (1989), Chapter 1, §1, Lemma 1.1 and its proof, printed
  pp. 3–4, PDF pp. 17–18. Source ID `arthur-clozel-1989-base-change`.
