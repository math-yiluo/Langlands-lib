# Complementary triangular marginals of a real matrix Fourier transform

`Langlands.Global.RankinSelbergGlobal.RealSquareFourier.RealSquareFourierMarginalStatement`
is a projection–slice identity for square real matrix Schwartz functions. It is
an internal ingredient for the Godement–Jacquet coefficient integrals towards
`RealPlaceFunctionalEquationStatement`.
It is proved by `realSquareFourierMarginal`.

Fix a dimension $n$ and a character parameter $b\in\mathbb R^\times$. Write
$\psi_b(x)=\exp(2\pi i b x)$ and $d_b x=\sqrt{|b|}\,dx$, the Library's
`realSelfDualMeasure b`. Use the product of this measure in every integrated
entry. For $d\in\mathbb R^n$ and $u$ a list of strictly upper entries, write
$T(d,u)$ for `upperTriangularEntries d u`, the upper triangular matrix with
diagonal $d$ and strictly upper entries $u$. The Schwartz function
`upperMarginal b Φ` is

\[
 \Phi_U(d)=\int \Phi(T(d,u))\,d_b u .
\]

`matrixTransform b Φ` is the Schwartz function

\[
 \widehat\Phi_b(X)=\int_{M_n(\mathbb R)} \Phi(Y)\psi_b(\operatorname{Tr}(X^{\mathsf T}Y))\,d_bY .
\]

The exact formulas for these two functions are `upperMarginal_apply` and
`matrixTransform_apply`. The statement is

\[
 \int \widehat\Phi_b(T(d,l)^{\mathsf T})\,d_b l
   = \texttt{realFourierTransform}\ b\ (\Phi_U)\ d
   = \int \Phi_U(t)\psi_b\bigl(\textstyle\sum_i t_i d_i\bigr)\,d_bt.
\]

The integral on the left therefore uses the **lower** triangular slice of the
matrix transform. The transpose cannot be dropped. In Jacquet's convention
$\widehat\Phi(X)=\int\Phi(Y)\psi(-\operatorname{Tr}(X^{\mathsf T}Y))\,dY$,
so $\psi=\psi_a$ there corresponds to $b=-a$ here, with the same measure
since $\sqrt{|-a|}=\sqrt{|a|}$.

## Lean proof

Reindex the matrix entries as $(d,u,l)$ (diagonal, strictly upper, strictly
lower). The reindexing of Euclidean spaces is a linear isometry. Restrict to
$l=0$ and integrate over $u$ using the Library's Schwartz marginal construction;
this gives a Schwartz diagonal marginal. The matrix Fourier transform is the
ordinary Euclidean Fourier transform after flattening the indices, scaling the
frequency by $-b$, and multiplying by the product of the entry densities.
The formula for the transform follows from the volume-preserving Euclidean
coordinate identification and the product-measure equivalence for currying
matrix entries.

On the reordered product, `SchwartzFourierMarginal.schwartzFourierMixedSlice`
identifies the integral over the last Fourier frequency, at middle frequency
zero, with the diagonal transform of the first marginal. Writing $c=\sqrt{|b|}$
and $q$ for the number of strictly upper entries, the matrix transform brings
$c^{n+2q}$ and the lower marginal measure brings $c^q$. Changing variables by
$-b$ in the lower frequencies contributes $|b|^{-q}=c^{-2q}$. This leaves
$c^n c^q$, the densities of the diagonal Fourier integral and the upper
marginal, respectively.

## Source and scope

Hervé Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
`jacquet-2009-archimedean-rankin-selberg`, §2 (p. 3, Fourier convention),
§4.7 (pp. 30–31, (4.3), (4.4) and Proposition 4.4). The projection–slice
identity is a derived coordinate calculation, not a quotation of a
separate theorem in the article. The implementation is the real-coordinate
analogue of the Library's `ComplexSquareFourierMarginal`. It does not assert
Iwasawa integration, the identification of any matrix coefficient integral
with a diagonal one, or a Rankin–Selberg functional equation.
