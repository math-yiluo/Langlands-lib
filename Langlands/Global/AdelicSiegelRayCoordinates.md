# Removing the integral part of a fundamental Siegel ray

The weak simple-root chamber consists of points with every simple-root logarithm at
least \(\log t\). Suppose that the supplied ray generator \(r\) has log step \(h>0\)
at \(\alpha\) and zero log at every other simple root. For any chamber point \(a\),
`AdelicSiegelRayCoordinatesStatement` writes \(a=r^n b\) with \(b\) in the same chamber.
The log at \(\alpha\) of \(b\) lies in \([\log t,\log t+h)\), and the other simple-root
logs agree with those of \(a\).

The proof takes \(n\) to be the natural-number floor of
\((\log|\alpha(a)|-\log t)/h\). Multiplicativity of the character norm gives the log
identity at each root. The two floor inequalities prove the chamber condition and
the bound on the remainder. If \(0<q<1\), the upper floor inequality also yields
the exponential majorant on \(q^n\), with rate \(-\log q/h>0\) in the original root
logarithm.

This integer-ray computation uses the simple-root coordinates of Delorme,
*On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023), 109107,
§2, PDF pp. 6–7, and the singled-out root direction in Lemma 3.10(i), PDF pp. 15–16.
The registered PDF is `Delorme--On the spectral theorem of Langlands--2023.pdf`,
SHA-256 `9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`,
under `delorme-2023-spectral-theorem-langlands`.
