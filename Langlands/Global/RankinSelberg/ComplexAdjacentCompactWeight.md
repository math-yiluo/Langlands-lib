# A common compact weight for the adjacent-rank square tests

Let \(\kappa\) be a finite Haar measure on \(U(r+1)\) and \(\eta\) a
continuous complex multiplicative character. If the left unitary
translates of a square Schwartz test \(\Phi\) span a finite-dimensional
space, `complexAdjacentCompactWeight` gives a continuous weight \(w\)
whose own left translates also span a finite-dimensional space. The
average of \(w(k)\eta(\det k)^{-1}\Phi(k^{-1}X)\) equals \(\Phi(X)\).

The same weight reproduces the square Fourier transform
\(\widehat{\Phi}_a\) with integrand
\[
  w(k)\eta(\det(k^{-\mathsf T}))\,\widehat{\Phi}_a(k^{\mathsf T}X).
\]
The proof first applies `complexLocalCompactMatrixWeight` to the
inverse character. It then uses `complexSquareFourierUnitaryAverage`
to take the square Fourier transform of that reproducing average.
Since \(\det(k^{-\mathsf T})=(\det k)^{-1}\), the scalar in the
ordinary average is also the determinant twist in the transformed one.

This is an auxiliary form of the compact averaging used to separate the
matrix coefficients in Jacquet's adjacent-rank calculation. See
Section 8.3 of Hervé Jacquet, *Archimedean Rankin–Selberg Integrals*,
2009, DOI `10.1090/conm/489/09547`.
