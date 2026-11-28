# Real Lie derivatives on the canonical adelic quotient

Let \(F\) be a number field and \(G\) an affine, locally finite-type
connected reductive group over \(F\). Use the canonical measure on
\([G]=A_G G(F)\backslash G(\mathbb A_F)\) and the archimedean Lie group
structure from a smooth relative dimension of \(G\). Let \(R\) be right
translation on \(L^2([G])\), restricted along the archimedean inclusion.

`CanonicalL2LieDerivativeStatement` takes a vector \(w\) smooth for this
restriction and a complex function \(\phi\) on \(G(\mathbb A_F)\) that is
left invariant under \(A_G G(F)\) and smooth on each archimedean slice.
Assume that \(\phi\) represents \(w\) almost everywhere on \([G]\).
For each real tangent direction \(X\) at the identity of \(G(F_\infty)\),
the Hilbert-space orbit derivative \(dR(X)w\) is represented almost everywhere
by differentiating the slice of \(\phi\) at the finite component of each
representative. Both derivatives use positive right translation. The
almost-everywhere equality gives square integrability of the pointwise
derivative on the quotient.

The statement extracts the compatibility of the two Lie actions used when
realizing smooth vectors as functions on \([G]\). Getz–Hahn,
*An Introduction to Automorphic Representations*
(`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`),
defines the real orbit derivative in §4.2, printed pp. 106–107
(PDF pp. 121–122), and uses the realization in \(L^2([G])\) in the proof
of Theorem 6.6.4, printed p. 172 (PDF p. 186). For a curve through the
identity with tangent \(X\), the Hilbert-space difference quotients
converge in norm and a sequence converges almost everywhere. The same
quotients of \(\phi\) converge pointwise by smoothness of its slices. This
argument applies to any smooth vector and representative as above.
