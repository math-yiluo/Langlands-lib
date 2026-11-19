# Integrability from decay in logarithmic Iwasawa coordinates

For every compatible quotient measure \(D\), the preceding box estimate
gives a positive threshold \(b\). If an almost everywhere strongly
measurable complex function \(f\) has norm at most
\(c\exp(-b\sum_i |x_i|)\) on every representative
\(\operatorname{diag}(e^{x_i})k\), then it is integrable for \(D\).

On the box at \(m\), the bound \(|m_i|\le |x_i|+1\) gives
an upper bound \(c\exp(b(r+1))\exp(-b\sum_i |m_i|)\) for the norm.
Multiply this bound by the box mass and sum over the covering. Taking
\(b=1+\log B\) makes the resulting ratio \(B e^{-b}\) less than one.
The sum in each integer coordinate converges by comparison with the
geometric series in the absolute value, with two signs. The finite
product of these sums is obtained by splitting off one coordinate at a
time. The resulting finite upper bound on the integral of the extended
norm gives absolute integrability.

This is the integration estimate used in the implementation of the
convergence implication. Its role corresponds to the use of
Jacquet's Lemma 3.5 on printed and PDF p. 14 of *Archimedean
Rankin–Selberg integrals* (2009).
