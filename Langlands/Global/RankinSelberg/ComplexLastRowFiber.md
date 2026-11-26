# The last-row fiber of the complex unipotent quotient

Write \(G=\mathrm{GL}_{k+2}(\mathbb C)\), \(N\) for its upper unipotent subgroup
and \(G_1=\mathrm{GL}_{k+1}(\mathbb C)\) with upper unipotent \(N_1\). The last
row of \(g\in G\) is invariant under left multiplication by \(N\). This module
computes the pushforward of an integrable function on \(N\backslash G\) along
the last row, and the value of its density at the last row of any \(g\), in
terms of an integral over \(N_1\backslash G_1\).

## Main theorem

`ComplexLastRowFiber.lastRowFiber k D D'` takes compatible quotient measure data
`D : ComplexQuotientMeasureData (k + 1)` and `D' : ComplexQuotientMeasureData k`.
It gives constants \(c_0,c>0\) such that every continuous, left
\(N\)-invariant \(F\colon G\to\mathbb C\) with \(q\mapsto F(q)\) integrable on
\(N\backslash G\) has an integrable function \(\Psi\) on \(\mathbb C^{k+2}\) with

* \(\int_{N\backslash G}\Theta(\text{last row of }g)\,F(g)\,dq
  = c_0\int_{\mathbb C^{k+2}}\Theta(\eta)\Psi(\eta)\,d\eta\) for every measurable
  \(\Theta\) with \(|\Theta|\le 1\);
* for every \(g\in G\) such that \(h\mapsto|\det h|_{\mathbb C}^{-1}
  F(\mathrm{diag}(h,1)g)\) is integrable on \(N_1\backslash G_1\),
  \[
  \Psi(\text{last row of }g)=c\,|\det g|_{\mathbb C}^{-1}
  \int_{N_1\backslash G_1}|\det h|_{\mathbb C}^{-1}F(\mathrm{diag}(h,1)g)\,dh .
  \]

Here \(|z|_{\mathbb C}=\|z\|^2\), and `lowerFunction F h` is
\(|\det h|_{\mathbb C}^{-1}F(\mathrm{diag}(h,1))\), with `pad₁` the inclusion
\(h\mapsto\mathrm{diag}(h,1)\).

## Construction of \(\Psi\)

Choose a continuous normalizing function \(\rho\ge0\) for \(N\)
(`exists_continuous_isNormalizingFunction`), so that the quotient integral of a
left-invariant function equals the group integral of \(\rho F\)
(`IsCompatible.integral_descend_eq`). The group Haar measure of `D` is a positive
multiple of `complexGeneralLinearHaar`, whose image on matrices is
\(|\det X|_{\mathbb C}^{-(k+2)}\) times Lebesgue measure on the invertible locus
(`integral_complexGeneralLinearHaar`, `lintegral_complexGeneralLinearHaar` and
`integrable_complexGeneralLinearHaar_iff`; `matrixDensity` is the weighted
function extended by zero). Lebesgue measure on matrices is the product of the
last row and the first rows (`joinRows`), and
`fiber k F ρ η` is the integral of the weighted density over the first rows with
last row \(\eta\). Fubini gives the first assertion in `integral_lastRow_eq`.

## The point formula

`fiber_lastRow` moves the last row of \(g\) to the standard row \(e\) by the
substitution \(A\mapsto Ag\) in the first rows. Lebesgue measure of the
\((k+1)\times(k+2)\) first rows scales by \(|\det g|_{\mathbb C}^{-(k+1)}\)
(`integral_rowsMul`), and the matrix density scales by
\(|\det g|_{\mathbb C}^{-(k+2)}\) (`matrixDensity_mul`). Solving for the
original fiber, the fiber at the last row of \(g\) equals
\(|\det g|_{\mathbb C}^{-1}\) times the fiber at \(e\) of the right translates
\(F(\cdot g)\) and \(\rho(\cdot g)\); the latter is again normalizing.

At \(e\) the first rows split into a leading square block \(h\) and a last column
\(u\) (`splitRows`), and the matrix is `blockMatrix k (u, h)`,
\(\begin{pmatrix}h&u\\0&1\end{pmatrix}=\begin{pmatrix}1&u\\0&1\end{pmatrix}
\mathrm{diag}(h,1)\) (`blockMatrix_val`). Its determinant is \(\det h\)
(`det_blockMatrix`). Left invariance of \(F\) removes the unipotent factor,
so the inner integral over \(u\) is
\(|\det h|^{-(k+2)}_{\mathbb C}F(\mathrm{diag}(h,1))\) times the column mass
`columnMass k ρ h` \(=\int\rho\bigl(\begin{pmatrix}1&u\\0&1\end{pmatrix}
\mathrm{diag}(h,1)\bigr)\,du\) (`integral_blockMatrix`). The published block Haar
formula `ComplexJacquet.complexLocalUnipotentBlockMeasure` writes the Haar
measure of \(N\) as a positive multiple of the image of \(N_1\times\mathbb
C^{k+1}\) under \((n',u)\mapsto\begin{pmatrix}n'&u\\0&1\end{pmatrix}\)
(`blockJoin_eq`). Hence a fixed multiple of the column mass is a normalizing
function for \(N_1\) (`isNormalizing_columnMass`). Integrating over \(h\) with
the Haar density on \(G_1\) and descending to \(N_1\backslash G_1\) with this
normalizing function gives `fiber_lastBasis`. Absolute integrability of the
block integrand, needed for Fubini, is checked on nonnegative integrals by the
same chain of identities (`lintegral_enorm_blockMatrix`).

## Source and provenance

This is derived measure-theoretic infrastructure for the last-row localization
of H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §6.2,
Propositions 6.1 and 6.2, author pp. 41–42 (registered source
`jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`). A related
quotient measure formula appears in Jacquet's §14.2, proof of Lemma 14.1, author
p. 106: \(f\mapsto\int f\begin{pmatrix}g&0\\x&h\end{pmatrix}dx\,
|\det g|^{-1}dg\,d^\times h\) is an invariant measure on
\(N_{r+1}\backslash G_{r+1}\), with \(g\) in \(N_r\backslash G_r\); the proof here uses only the compatibility of the
supplied quotient measures, the published normalizing-function rules, the
published Haar density on complex matrices and the published block Haar formula
for the unipotent group.
