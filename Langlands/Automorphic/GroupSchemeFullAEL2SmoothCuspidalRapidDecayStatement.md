# Rapid decay of smooth vectors in the full cuspidal Hilbert space

Let \(G\) be a connected reductive affine locally finite type group
scheme over a number field \(F\). Use the supplied parabolic-dynamic
statement and a central morphism from a finite-rank split torus whose
restriction on rational characters is injective with finite-index
image. In the specified split-torus coordinates, each positive real
coordinate is embedded diagonally across the infinite places, and
the finite component is the identity. Write \(A_i\) for its image in
the adelic group. For a split component, `imageSubgroup_eq_canonicalSubgroup`
identifies \(A_i\) with \(A_G\) of (2.20).

The norm-one subgroup is the common kernel of the rational character
norms. Assume right invariance of its Haar measure. The positive
rational quotient is \(Q=A_iG(F)\backslash G(\mathbb A_F)\), with
the norm-one rational quotient Haar measure transported through the
inclusion-induced homeomorphism as in (2.22). Its full \(L^2\) cuspidal
subspace tests absolute integrability and vanishing almost everywhere
for every proper rational parabolic radical.

`GroupSchemeFullAEL2SmoothCuspidalRapidDecayStatement` applies to a
class in that subspace whose archimedean orbit map is real
\(C^\infty\) and whose finite action fixes it on an open subgroup.
It gives a continuous representative \(v\) of the class. Its pullback
to the adelic group has plot-smooth infinite slices and a common open
finite right level. For every proper rational parabolic with
unipotent radical \(N\) and every \(g\in G(\mathbb A_F)\), the integral
of \(v([ng])\) over \(N(F)\backslash N(\mathbb A_F)\) vanishes.
`properParabolicQuotientMeasure` gives the quotient Haar measure total
mass one. This is the trivial-character unipotent period in (9.7)
with a fixed choice of scale.

Fix a closed embedding \(\rho:G\to\mathrm{GL}_n\) with \(n>0\).
The height \(H_\rho=\texttt{RepresentationGrowth.adelicHeight}\)
is the product over places of the normalized local entry maxima
of \(\rho(g)\) and its inverse, multiplied by
\(n^{\sum_{v\mid\infty}v.\mathrm{mult}}\). The real and complex
archimedean multiplicities are one and two. The unscaled product
is the norm of the doubled embedding in (6.3), (6.7) and (6.8).
The fixed factor changes only the bound for each given power.

One subset \(\Omega\subset G(\mathbb A_F)^1\) meets every
rational left coset in the norm-one group. It works for all the
smooth vectors in the proposition. For each such representative
\(v\), each archimedean right-orbit derivative word
\(s\), and each \(m\in\mathbb N\), the function
\(\lvert D_s(v\circ\mathrm{mk})(x)\rvert H_\rho(x)^m\) is bounded
for \(x\in\Omega\). Each direction differentiates the right orbit
at the identity of the infinite group. The empty word gives the value.

This is a reduced-representative form of Getz–Hahn Corollary 9.6.5
with derivative bounds. Use the finite smooth convolution expansion
of the vector, apply the convolution decay estimate to each term
on the same reduced set, and take the finite sum of the bounds.
The statement uses an adelic matrix height on that set. The book's
Definition 9.6.1 uses the root coordinates of a chosen Siegel set.
The pointwise period clause uses the comparison for continuous
representatives of cuspidal \(L^2\) classes.

## Source

- `getz-hahn-2024-automorphic-representations`,
  SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
  Section 2.6, (2.19)–(2.22) and Lemma 2.6.2, printed pp. 68–69
  (PDF pp. 85–86). The doubled embedding and adelic norm in (6.3)
  and (6.7)–(6.8), printed pp. 158 and 161 (PDF pp. 172 and 175).
  The translated period in (9.7) and Lemma 9.2.3, printed p. 243
  (PDF p. 255). Definition 9.6.1, Theorem 9.6.4
  and Corollary 9.6.5, printed pp. 263–264 (PDF pp. 275–276).
