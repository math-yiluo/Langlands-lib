# Schwartz row multiplication on real smooth Whittaker coefficients

For a jointly continuous complex Banach representation of \(GL_n(\mathbb R)\),
let \(L\) be a continuous scalar functional on its genuine smooth vectors
that transforms by the standard upper-unipotent character at a nonzero
real scale \(a\). Write \(W_v(g)=L(\pi(g)v)\). Given a smooth vector \(v\),
a smaller positive rank \(m<n\) and a Schwartz test \(\Phi\) on rows of
length \(m\), the construction gives one smooth vector \(w\) such that
\[
W_w(\operatorname{diag}(g,I_{n-m}))
 = W_v(\operatorname{diag}(g,I_{n-m}))\,\Phi(e_mg)
 \qquad (g\in GL_m(\mathbb R)).
\]
Here \(e_m\) is the last coordinate row.

Average the genuine smooth orbit by the unipotent column immediately after
the leading block, with scalar weight the Schwartz Fourier transform of
\(\Phi\) at scale \(-a\). The column matrix and its inverse both grow at
most linearly in the column variable. Moderate growth in each genuine
word seminorm and Schwartz decay give Bochner integrability of the
weighted word coordinates. The smooth-vector integral of these
coordinates commutes with the functional composed with the action of
\(\operatorname{diag}(g,I_{n-m})\).

Moving the column past that diagonal changes a column \(x\) to \(gx\).
The standard unipotent character then reads the last entry of \(gx\),
which is the pairing of \(e_mg\) and \(x\). Fourier inversion with the
specified real self-dual measure gives \(\Phi(e_mg)\).

This is the first assertion of Proposition 6.1 in H. Jacquet,
*Archimedean Rankin–Selberg Integrals* (2009), author-posted pp. 41–42,
for real smooth vectors realized in the stated Banach representation.
Proposition 6.2 uses this assertion with a compactly supported row test
in the proof of the rank-raising inclusion.
