# Rapid decay of smooth cuspidal convolutions

`Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeFullAEL2CuspidalConvolutionRapidDecayStatement`
concerns an affine locally finite type connected reductive group \(G\) over
a number field \(F\). It takes the parabolic-dynamic statement used to
construct the canonical proper radical family and a central map
\(i:T\to G\) from a torus with a specified finite split presentation.
Pullback along \(i\) on rational characters is injective with finite-index
image. Haar measure on the common kernel \(G(\mathbb A_F)^1\) of the
rational character norms is assumed right invariant. Fix a closed matrix
embedding \(\rho\) of positive size.

The positive real coordinates in the split presentation of \(T\) are
embedded diagonally at the infinite places. Their image \(A_i\) gives the quotient
\(Q=A_iG(F)\backslash G(\mathbb A_F)\). Its measure is the pushforward of
the Library's Haar quotient measure on \(G(F)\backslash G(\mathbb A_F)^1\)
along the inclusion-induced homeomorphism. The input \(\phi\) lies in the
closed almost-everywhere cuspidal subspace of \(L^2(Q)\) for the canonical
proper radical family. The function \(f\) is a full-group adelic test
function with its Haar integrability witness. It is continuous, has
smooth archimedean slices and compact support, and has open levels for
left and right finite adelic translation. The pointwise formula is
\[
  \psi(x)=\int_{G(\mathbb A_F)} f(a)\,\phi([xa])\,da,
\]
using the chosen \(L^2\) representative and the original left Haar measure
on the full group. The assertion gives an adelically smooth \(\psi\), with
smooth archimedean slices and an open right finite adelic level. It equals
the pullback of a continuous quotient function \(v\). Almost everywhere
for the quotient measure, \(v\) equals the class obtained by Bochner
integrating the original cuspidal right action against \(f\).

One subset \(\Omega\subset G(\mathbb A_F)^1\) works for all \(f\) and
\(\phi\). Every norm-one point has a rational left translate in \(\Omega\).
For each archimedean orbit derivative word \(s\), including the empty word,
and each \(m\in\mathbb N\), there is \(B\ge 0\) with
\[
   |D_s\psi(x)|\,H_\rho(x)^m\le B\qquad (x\in\Omega),
\]
where \(H_\rho\) is `RepresentationGrowth.adelicHeight`. The constant
can depend on \(f,\phi,s,m\). The height is evaluated on the reduced set.

The smooth-convolution result is derived from Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Theorem 9.6.4,
printed p. 264 (PDF p. 276).
For a split component \(i\), the Library identifies \(A_i\) with the
canonical \(A_G\) of (2.20), and transports the quotient measure by the
inclusion of (2.22) in §2.6, printed pp. 68–69 (PDF pp. 85–86).
The source tests on \(A_G\backslash G(\mathbb A_F)\). Here the integral
uses full-group tests with the action on \(Q\). The reduction-theoretic
proof chooses one norm-one Siegel cover and the bound evaluates the
matrix height on that cover. This uses the reduced-representative
setting of Definition 9.6.1, printed p. 263 (PDF p. 275), which states a
root-coordinate estimate on each Siegel set. The derivative assertion is derived from
the smoothing identity of Mœglin–Waldspurger, *Spectral decomposition and
Eisenstein series* (1995), I.2.5(b), printed p. 27 (PDF p. 10 in
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`). Each
derivative is convolution by another test kernel, so the same set of
representatives supports the decay estimate.
