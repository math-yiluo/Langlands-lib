# Translation-covariant distributions on a real vector space

`TranslationCovariantDistributionStatement` works on a finite-dimensional real normed vector space with a Borel structure and an additive Haar measure \(\mu\). If a continuous linear functional on compactly supported smooth tests transforms under \(f(x)\mapsto f(x+z)\) by a smooth additive character \(\chi(z)\), it is a scalar multiple of
\[
 f\longmapsto \int f(x)\chi(-x)\,d\mu(x).
\]

The proof chooses a real smooth bump \(\rho\) with positive integral. For each test \(f\), the families \(f(x)\rho(x-z)\) and \(\rho(x)\chi(-z)f(x+z)\) have uniformly compact support in \(z\), and each has a fixed compact support in \(x\). Translation covariance makes their distribution values equal for each \(z\). `DistributionFamilyIntegral` permits integrating these values in \(z\). The first integrated test is \((\int\rho)f\). Translating the integration variable in the second gives \(\rho(x)\chi(x)\int f(y)\chi(-y)\,d\mu(y)\). Division by \(\int\rho\) gives one proportionality constant for every test.

The negative-character integral is the transverse Fourier functional used in Jacquet, *Archimedean Rankin–Selberg Integrals*, proof of Proposition 14.1, pp. 103–104 of the author-posted edition. The proportionality follows from translation covariance and the compact test integral argument above.
