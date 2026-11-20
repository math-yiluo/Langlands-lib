# The Godement section in the complex open-cell Jacquet integral

`openCellIntegral` integrates an upper-Borel inducing function at \(w_nug\)
against the positive first-superdiagonal character with parameter \(a\).
When these integrals are absolutely convergent and the unipotent measure is
right invariant, translation of the integration variable by a fixed
unipotent \(u_0\) gives the left Whittaker factor
\(\theta_a(u_0)^{-1}=\theta_{-a}(u_0)\).

`openCellIntegral_godementSection` proves the comparison in Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), §7.2, (7.5)–(7.6), pp. 47–48,
for an absolutely integrable joint kernel. It uses a supplied product
measure, which can be arbitrary, on the larger upper unipotent group via the
ordered coordinates
\((u,v)\mapsto\operatorname{diag}(u,1)n(v)\), with \(n(v)\) the last-column
unipotent. The character splits into the smaller first-superdiagonal
character and \(v\)'s last-coordinate character. The trailing rows of
\(w_{m+1}\operatorname{diag}(u,1)n(v)g\), with \(m=r+1\), then give the square
block \(w_m u\) and the column \(w_m u v\) before right multiplication by
\(g\).

Right translation \(h\mapsto h w_m u\) preserves the supplied smaller-group
measure. Fubini and the product integral separate the smaller open-cell
Jacquet integral and the last-column Fourier integral. The outer
determinant character has the exponent from (7.6). The two Weyl
determinants contribute the explicit factor \(d((-1)^m)\) in the
upper-Borel formula. The test in the resulting kernel is the right
translate by \(g\).

The comparison assumes joint absolute integrability. Establishing that
condition on a parameter chamber and comparing the continued open-cell
construction with the Library Whittaker model are separate steps.
