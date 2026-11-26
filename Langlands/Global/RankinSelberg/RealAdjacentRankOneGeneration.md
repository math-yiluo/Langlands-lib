# A normalized real \(GL_2\times GL_1\) test in the closed character chamber

`realAdjacentRankOneClosedChamber` proves that a single test has normalized
value one for the ordinary real \(GL_2\times GL_1\) integral at additive
scale \(1\). The parameter lists are two real characters \(c,d\) and one
real character \(e\), with \(\operatorname{Re} d \le \operatorname{Re} c\)
for their inducing exponents. The quotient measure data are arbitrary
compatible data at rank one. `realAdjacentRankOneGeneration` is the
strict-chamber specialization.

The leading-column test is the real Tate Gaussian of parity \(ce\). The
trailing-column test is the positive Fourier transform of the real Tate
Gaussian of parity \(de\). The latter transform multiplies its Gaussian
by \(i\) to the power of its parity, and the opposite-sign transform
recovers the original Gaussian. The separated rectangle is therefore
a polynomial Gaussian. Express it as a scalar times the coefficient-one
Gaussian polynomial pulled back by scalar dilation by \(\sqrt{\pi}\).
The scalar group translation of its Godement section commutes with the
orthogonal action. The published polynomial Gaussian section theorem
then places the dilated section in the compact-finite principal series.

The rank-one coefficients in the adjacent unfolding are the determinant
characters of \(d\) and \(e\). Multiplicativity of the character of \(e\)
separates the unfolded integral into a quotient Tate integral with
character \(de\) and a matrix Tate integral with character \(ce\).
The Gaussian evaluations give the two Gamma factors of the prescribed
pair factor on a right half-plane, with a nonzero constant from the Haar
comparisons and the Weyl scalar.

Vary the leading exponent with its sign parity fixed. On the orthogonal
group the Gaussian section factors into a fixed angular monomial with
its determinant sign and a radial Tate moment. Orthogonality fixes the
squared norm of the last row, which gives this separation. The moment
is continuous throughout the closed chamber since its shifted Tate
argument has positive real part. The moment at a strictly dominant
reference exponent is nonzero. Its vanishing would make the section
zero on the orthogonal group and hence on the full group, contradicting
the unfolded Gaussian value.

The canonical Jacquet family of the reference compact profile,
multiplied by the ratio of radial moments, agrees with the Gaussian
column coefficient in the strict chamber by the absolutely convergent
open-cell formula. The independently entire leading-character column
family and the canonical family are both continuous at the boundary.
Taking the leading exponent to the given exponent through real positive
increments gives the same equality in the closed chamber. The canonical
map puts this coefficient in the uniform Whittaker model, hence in the
ordinary model. Dividing it by the nonzero unfolding constant gives a
single test with entire normalization equal to one.

The calculation uses Jacquet, *Archimedean Rankin–Selberg integrals*
(2009), author-posted pp. 43 and 46–48 for the Godement section and
Jacquet coefficient, and §8.3, equation (8.3), pp. 58–59 for the
adjacent unfolding. It is a direct character-chamber case of the
generation conclusion in Theorem 2.7(i), p. 10. The registered source is
`jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
