# Continuing the complex Godement Whittaker value in the added exponent

Fix the smaller inducing list in the strict upper-Borel chamber and a
compact-finite input vector for that list. The open-cell integral gives
a fixed vector in the exact Library Whittaker model with parameter
\(-a\), where \(a\) is the integrating character parameter.
The larger Godement section adjoins the character with exponent
\(d.\mathrm{exponent}+s\) at the first position and keeps its angular
weight fixed.

`rightTest` pulls the rectangular Schwartz function back by right
multiplication with the larger group argument. The transformation
is a continuous linear equivalence. The positive last-column Fourier
transform of this test is Schwartz for the supplied scalar Haar
measure. The (7.6)–(7.7) column change therefore proves that the
iterated integral is entire in its determinant exponent at this
fixed smaller-rank vector.

`continuedValue` evaluates the integral at the shifted exponent,
and includes the determinant power of the larger group argument.
The upper-Borel factor \(d((-1)^m)\) stays fixed because the shifted
absolute value at \((-1)^m\) is one. The chamber comparison identifies
this entire function with the larger open-cell Godement value wherever
the new first exponent and the fixed tail form the strict chamber.
The initial test is Schwartz with compact support in the full-row-rank
locus. The result is pointwise in the larger group argument.

The implemented continuation is the one-parameter specialization of
Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §7.2,
(7.6)–(7.7) and Proposition 7.2, pp. 48–49.
