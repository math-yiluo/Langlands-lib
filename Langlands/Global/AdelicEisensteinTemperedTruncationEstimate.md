# Truncated pairing of Eisenstein series with a logarithmically square-integrable form

The proposition is the characteristic truncation comparison of Delorme,
*On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023),
109107, Theorem 7.1, pp. 25–26, for the test forms used in
`WavePacketWeakConstantTermOrthogonalityStatement`. The published PDF in
`delorme-2023-spectral-theorem-langlands` has SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.

For the standard family the statement selects a reference compact with
minimal-parabolic Iwasawa coverage, maximal compact inverse images in the
standard Levi subgroups, and the positive-torus commutation property. The
compact factors obey (7.1), and the characteristic regions cover the
norm-one quotient as the truncation vector varies. The positive constants
`vol` include the Haar normalization comparisons for the specified quotient
measures and are chosen before the forms. The tested form has the unitary
central character and form-level logarithmically weighted \(L^2\) condition
from the orthogonality statement, for a closed matrix embedding. Applying
Delorme's Theorem 7.1 at this input requires establishing its temperedness
condition. In the source, Proposition 3.5 starts with weighted \(L^2\)
bounds for all archimedean derivatives, with a common exponent. The
inducing form belongs to the Library's `IsSquareIntegrableInducedForm`. A
supplied continuation is pointwise holomorphic at the imaginary parameters
and agrees with the convergent series in the regular chamber.

The regularity of \(T\) is a positive lower bound on each simple root on the
relative coroot space. The sector imposes the further lower bound
\(\alpha(T)\geq\delta\|T\|\) for all simple roots. The coordinates define
finite-dimensional norms on \(T\) and on the logarithm of the positive
central translate. The source uses Euclidean norms and the bound is
invariant under passage to equivalent norms after changing constants.

The fixed affine labels give a common list of allowed spectral exponents
for all central translates. The labels in (7.12) are the differences of
Weyl-transformed Eisenstein parameters and weak constant-term exponents.
On the generic region of the list, the expansion relation identifies the
exponential polynomials with the normalized pairings of the actual weak
constant terms, using the square-integrable first component from §3.4.
The region is open and dense in imaginary coordinates. Part (i) of the
source gives the holomorphic extension of the resulting sum near the
imaginary space. The statement records agreement on this sufficient
generic region. The explicit Weyl labels and polynomial coefficients in
(7.12) enter when computing the distribution of Proposition 7.8.

For a fixed sector and bounded imaginary parameter set, the constants of
the bound are independent of the varying parameter, truncation vector,
and central translate. The right hand side is
\(B e^{-\epsilon\|T\|}(1+\|Z\|^k)\). The integrable left term and the
holomorphic regularized term are the \(\Omega^T_{P_0}\) and
\(\omega^T_{P_0}\) of Theorem 7.1.
