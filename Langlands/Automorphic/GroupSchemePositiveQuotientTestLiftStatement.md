# Lifting smooth tests from the quotient by the positive split centre

Let \(G\) be a connected reductive affine group scheme, locally of finite type
over a number field \(F\). Let \(T\) have a finite split-torus coordinate system
and a central homomorphism to \(G\). Restriction of rational characters along
this homomorphism is injective with finite-index image. Write \(A^+\) for the
intrinsic positive subgroup of \(T(\mathbb A_F)\), and write \(a x\) for the
product of its image with \(x\in G(\mathbb A_F)^1\).
The Library's `normOneProjection` identifies the quotient by the image of
\(A^+\) with \(G(\mathbb A_F)^1\).

`IsPositiveQuotientTestFunction` takes a continuous complex function \(f\) of
compact support on this norm-one group. Its pullback by `normOneProjection`
has plot-smooth infinite slices and is fixed under finite right and left
translation by open subgroups of \(G(\mathbb A_{F,f})\). The compact support
condition is on the quotient. The predicate concerns the quotient by the
positive central image before taking rational cosets.

`GroupSchemePositiveQuotientTestLiftStatement` says that every such \(f\)
is the average of an ambient compactly supported smooth bi-level test \(h\).
At every \(x\in G(\mathbb A_F)^1\) one has

\[
  \int_{A^+} h(a x)\,da = f(x).
\]

Here \(da\) is `normalizedPositiveHaarMeasure`. By
`measurePreserving_normOneDecomposition`, its product with the existing
norm-one Haar measure maps under multiplication to the existing ambient
Haar measure.

The lifting assertion is derived from the positive and norm-one
decomposition in Getz–Hahn (2024), §2.6, (2.19)–(2.22) and
Lemma 2.6.2, printed pp. 68–69 (PDF pp. 85–86). Equation (9.2), printed
p. 239 (PDF p. 251), defines the operator. Its test space, specified
on printed p. 240 (PDF p. 252) and used in Theorem 9.1.2 on printed
p. 241 (PDF p. 253), is the algebraic tensor product of compactly
supported smooth infinite-place tests on the quotient by \(A_G\)
and compactly supported locally constant finite-adelic tests. The Lean proposition
uses smooth pullback on infinite slices and the two finite translation
levels as its regularity hypotheses. The averaging identity comes
from multiplying the pullback by a smooth compactly supported function
of the positive coordinate whose integral is one.

Source `getz-hahn-2024-automorphic-representations`,
SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
