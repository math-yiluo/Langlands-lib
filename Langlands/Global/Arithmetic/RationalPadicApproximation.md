# Rational approximation in the real and p-adic topologies

This internal construction pulls the real and p-adic norms back to absolute
values on the rationals. They are nontrivial and inequivalent, as seen at
`2` and at the rational prime `p`. Abstract weak approximation therefore gives
a rational number close to prescribed rational numbers for both absolute
values. Individual density of the rationals in the reals and in `Padic p`,
followed by the triangle inequality with half-radii, gives simultaneous
approximation to arbitrary real and p-adic targets.

The construction `rationalMonicModel n c` is the polynomial `X^n` plus the
terms `c_i X^i` for `i<n`. It is monic of degree `n`, including `n=0`.
Coefficientwise simultaneous approximation to a monic p-adic polynomial
and to `realRootModel n` gives a rational monic polynomial of the same degree
with arbitrarily close p-adic coefficients and distinct real roots. The
real-root conclusion uses the explicit neighborhood in
`RealRootNeighborhood`. Separability descends along the rational-to-real
embedding.

This is internal derived content implementing the polynomial approximation
step motivated by Henniart (1984), Lemma 3.6, printed pages 34–35 (PDF pages
35–36), source `henniart-1984-gl3`, SHA256
`968076c8b63d4a94442c080040b684fe1f71b01a3c0933d111a49745369629f7`,
and the distinct-real-root condition in Henniart (2000), Section 3.3,
printed page 449 (PDF page 11), source `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
Worker 37 read those original passages. The explicit model and use of
Mathlib absolute-value weak approximation are not attributed to the source.
No number fields, actual primes, completion equivalences or Galois
comparisons are constructed here.
