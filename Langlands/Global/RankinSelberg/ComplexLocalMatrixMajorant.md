# A matrix majorant for the complex Jacquet comparisons

The convergence arguments in Jacquet’s §8.2 and §8.3 separate a Schwartz matrix test from a polynomial height bound on the translated Whittaker function. For \(n,M\in\mathbb N\), a Schwartz test \(\Phi\) on the square complex matrices, character data \(d\), and any Haar measure on \(\mathrm{GL}_n(\mathbb C)\), the lemma proves integrability of
\[
  \max(1,H(g))^M
  \left|\Phi(g)\,d.\mathrm{character}(\det g)\,(|\det g|^2)^s\right|
\]
whenever \(\operatorname{Re}(s+d.\mathrm{exponent})\ge n+M\). The determinant power uses the normalized absolute value \( |\det g|^2 \).

The matrix height is the sum of the squared Frobenius norms of a matrix and its inverse. Submultiplicativity of the Frobenius norm bounds both terms for a product. Taking the maximum with one gives the stated height inequality.

The absolute value of the determinant character shifts the real part of the determinant exponent by the real part of the character exponent. The existing height-weighted Schwartz estimate then gives integrability for the canonical matrix Haar measure at height orders zero and \(M\). Their sum controls the weight \(\max(1,H)^M\). Uniqueness of Haar measure transfers integrability to the prescribed Haar normalization.
