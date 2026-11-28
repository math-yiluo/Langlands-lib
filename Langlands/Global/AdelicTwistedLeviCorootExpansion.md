# Coroot expansions of twisted Levi pairings

`normalizedPairing_twistedComponent_corootExpansion` expands the normalized
Levi pairing of an inducing form twisted by `lam` and a component of unitary
exponent `mu`. Both arguments carry the same translate by a positive point
of the ambient split centre. The theorem assumes absolute convergence for
the untwisted component at every positive split-component point. At a
point whose logarithm is \(\sum_\alpha c_\alpha\check\alpha\), it gives
absolute convergence for the translated and twisted pairing and the value
\[
  \exp\!\left(\sum_\alpha c_\alpha(\lambda-\mu)(\check\alpha)\right)
  p(c)
\]
for a complex polynomial \(p\) in the relative coroot coordinates. The
conjugation of the second argument accounts for the sign of \(\mu\).

The proof lifts the ambient central point to the parabolic split component
using the nested split-component map. Its image in the ambient group
commutes with the norm-one Levi and compact factors, and its parabolic
half modulus is one. Moving the central point through those factors
changes the positive split-component point from \(x\) to \(y\).
The Iwasawa height of the resulting representative is the logarithm of
\(y\), so the inducing twist contributes a scalar to the whole integral.
The polynomial slice formula for the original component gives the
remaining integral. Its modulus at \(y\) cancels the normalizing factor at
\(x\). The character evaluated at the central lift multiplies the
polynomial by a scalar, and translation by the logarithm of the lift
substitutes affine linear forms into the polynomial.

`TwistedLeviPairingCorootExpansionStatement` and its proof
`normalizedPairing_finsetSum_corootExpansion` sum this formula over
finite sets of inducing labels and unitary component labels. Absolute
convergence allows the sum of components to pass through the integral.
The product of the label sets indexes the resulting terms, so several
terms may have the same difference parameter.

The formula is derived from the normalized Levi pairing and its
polynomial dependence in P. Delorme, *On the spectral theorem of
Langlands*, Advances in Mathematics 426 (2023), 109107, §3.4,
(3.7) and Remark 3.9, p. 15, and the translation and exponent difference
in (7.12), p. 25. The registered source
`delorme-2023-spectral-theorem-langlands` contains the published PDF
with SHA-256 `9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
