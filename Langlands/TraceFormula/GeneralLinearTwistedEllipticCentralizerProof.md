# The twisted elliptic centralizer theorem for a Weil restriction of `GL_n`

`Langlands.TraceFormula.generalLinearTwistedEllipticCentralizer.{u}` proves
`Langlands.TraceFormula.GeneralLinearTwistedEllipticCentralizerStatement.{u}`. The finite-place
regular ellipticity hypothesis gives a rational matrix `δ` with a regular elliptic cyclic
norm associate `γ` over the base field, by
`exists_sigmaElliptic_rational_matrix_of_isRegularElliptic_localNorm`.

`generalLinearWeilTwistedCompactQuotient` gives compactness of the rational centralizer
quotient. Use a rational twisted conjugation to arrange that the norm of `δ` is exactly the
scalar extension of `γ`. The equivalence `exactRegularNormCentralizerEquiv` then identifies
the twisted centralizer with the ordinary centralizer of `γ` over the ground-field adeles.
The fixed coefficients are the ground-field adeles by `adeleCoefficientAut_fixed_iff`.
Extending matrix coefficients raises the determinant norm to the extension-degree power by
`full_ideleNorm` and `ideleNorm_ideleInclusion`, so the equivalence restricts to the norm-one
centralizers. Undo the rational conjugation and apply the Weil coordinate comparison. The
resulting continuous surjection sends rational points to rational points. The compact
quotient of the ordinary centralizer, supplied by `adelicRegularCentralizerCompactQuotient`,
therefore maps continuously onto the desired rational quotient.

`generalLinearWeilTwistedClosedOrbit` supplies closedness. In matrix coordinates the orbit is
a characteristic-polynomial fibre of the ordered norm, using specialization at maximal
ideals of the base adele ring and idempotent patching of the resulting matrix intertwiners.
Twist-fixed positive scalars allow the conjugating matrices to have determinant norm one.
The proof transports the closed orbit to the actual Weil norm-one group.

Regularity of the compatible quotient measure gives finiteness on compact sets, so the
compact rational quotient has finite total mass. For the second conclusion,
`twistedOrbitFunction_integrable_of_isClosed` uses the homeomorphism from the centralizer
left coset space to the closed orbit. The pullback of the test function along this orbit
map is continuous with compact support. Regularity of the compatible measure makes it
integrable.

## Sources

- Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula* (1989), Chapter 1, §1 and Lemma 1.1, printed pp. 3–4 (PDF pp. 17–18), give the
  ordered norm and the centralizer comparison used at an exact rational norm.
  Registered source `arthur-clozel-1989-base-change`, SHA-256
  `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
- Getz and Hahn, *An Introduction to Automorphic Representations* (2024), §2.6,
  printed pp. 68–69, give the positive scalar and norm-one conventions. Theorem 18.2.5,
  printed p. 479 (PDF p. 486), uses closed orbits. Equations (18.31)–(18.32) and Corollary
  18.5.1, printed pp. 487–488 (PDF pp. 494–495), give the twisted centralizer, its volume,
  and its orbital integral in the simple twisted trace formula.
  Registered source `getz-hahn-2024-automorphic-representations`, SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
