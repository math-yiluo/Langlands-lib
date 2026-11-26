# Smooth compact rectangle sections in the real parabolic cell

`RealParabolicCompactSectionStatement` constructs a smooth function on the actual real general linear group from two smooth functions on the Levi blocks, two complex determinant powers, and a smooth compactly supported rectangle kernel. In lower block coordinates with invertible diagonal blocks \(A,S\), the section takes the value

\[
 |\det A|^{z_1}|\det S|^{z_2} f(A)g(S)\Phi(Y)
 \quad\text{on}\quad
 \begin{pmatrix} A&AY\\ C&CY+S\end{pmatrix}.
\]

The complex powers use the positive real logarithm. The topological support of the section lies in the open cell where the leading block is invertible.

On that cell the rectangle and the second Levi coordinate are recovered as \(Y=A^{-1}B\) and \(S=D-CY\). Block elimination gives \(\det u=\det A\,\det S\), so the two factor functions and their determinant weights are smooth there. For compact rectangle support \(K\), the set of matrices admitting \(B=AY\) for some \(Y\in K\) is closed in the group. It is the projection of a closed set along a compact factor. At every point of this closed set, the same determinant identity forces \(A\) to be invertible. The section vanishes on the open complement of that set, which contains the singular-pivot locus.

This is the compact rectangle case of the open-cell section construction used in Jacquet, *Archimedean Rankin–Selberg Integrals*, §13.2, pp. 100–103, and Proposition 14.1, pp. 103–104 in the author-posted edition. The normalized lower-parabolic exponents are \(z_1=-n/2\) and \(z_2=m/2\). The statement concerns scalar smoothness, the values on the cell and the support condition. The representation covariance and split Whittaker evaluation are further properties of the induced section.
