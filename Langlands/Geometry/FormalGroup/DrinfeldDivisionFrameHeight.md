# Actual signed division heights on the globally coordinated frame

Drinfeld, *Coverings of p-adic symmetric regions* (1976), §2 A, printed
p. 109 (PDF p. 3), precomposes the framing with the inverse division-unit
action. The sign of its height uses the numerator-minus-denominator formula
in Harris, *Supercuspidal representations in the cohomology of Drinfel'd
upper half spaces* (1997), Appendix, printed p. 112 (PDF p. 38).

For a formal \(O_D\)-module over a coefficient field \(k\), choose a
uniformizer \(\pi\), a rank base \(q>1\), and a certificate
`HasPiHeight π q (H * d)`, where \(d\) is the reduced degree of \(D\).
This certificate includes \(\pi\)-divisibility. The division degree gives
an integral isogeny numerator after clearing a scalar denominator. Its
finite kernel rank is determined by the degree and the scalar kernel rank.
`twistQuasiIsogenyHeightPresentation` chooses such a presentation of the
actual inverse division action together with the equality of its signed
index to \(-H\operatorname{ord}(\operatorname{Nrd}(g))\).

The global-to-atlas map carries the extended division action to the
actual action on the restriction of the global law to any given
principal-open cover. This follows on order elements from the integral
chart comparison and extends to the rational tensor. Given an
\(O\)-algebra map \(k\to S\) into a commutative coefficient ring,
extending the ranked presentation along the map and then evaluating it on
all tests of the principal-open cover of \(\operatorname{Spec}(S)\) gives
the same signed index at every test. For the special frame \(\Phi\), the
scalar height \(d^2\) gives \(H=d\). Here \(q\) is the cardinality of the
residue field of \(K\), so the signed index is
\(-d\operatorname{ord}(\operatorname{Nrd}(g))\) in that rank base.
