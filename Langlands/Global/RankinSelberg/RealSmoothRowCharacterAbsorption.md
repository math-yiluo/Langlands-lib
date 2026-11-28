# Schwartz row absorption from additive covariance

`RealSmoothRowCharacterAbsorptionStatement` takes a jointly continuous
representation of the units of a finite-dimensional real Banach algebra
on a complex Banach space. Its scalar form is continuous and complex-linear
on the genuine word-derivative smooth carrier. A continuous family of
column elements has at most linear growth of its unit height in the column
variable. The Banach operator norms along the family are bounded by a
fixed nonnegative constant times a fixed natural power of that height.

Suppose acting by a column element before a given evaluating translate
multiplies the coefficient by the additive character of the pairing of
that column with the prescribed row. For every genuine smooth input
vector and every Schwartz test of the row, there is a single genuine
smooth vector realizing the multiplication at all evaluating translates.
The character has the supplied nonzero real additive scale.

Take the Schwartz Fourier transform at the opposite scale as the weight
in the column orbit. The individual word bounds follow from the operator
bound and inverse conjugation of the Lie directions. The linear height
bound and Schwartz decay make every word integrable. The genuine smooth
integral commutes with applying the scalar form after a fixed translate.
The covariance law and Fourier inversion identify the result with the row
value of the input test times the original coefficient.

This is the Fourier argument of Proposition 6.1, pp. 41–42, with the
growth and covariance assumptions explicit. Jacquet uses the row
multiplication of Proposition 6.2 in Lemma 14.1, p. 106, where one of the
two representations supplies the column action.
[H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), author-posted edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=41).

The registered source is `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.

`RealSmoothRowCharacterAbsorptionAllEvaluationsStatement` allows the continuous linear form to vary with the evaluation point. The averaged vector is independent of the form. Evaluating the same vector integral against each composed form gives the simultaneous identity. The fixed-form statement is its specialization.
