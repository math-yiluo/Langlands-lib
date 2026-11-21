# The square equation for a determinant-twisted compact coefficient

For a standard vector \(f\) with inducing characters \(e_i\), let
\(C(g)=\int w(k)f(kg)\,d\kappa(k)\). `complexAdjacentTwistedZeta`
gives the normalized square zeta equation for the coefficient
\(d(\det g)C(g)\). On the dual side the coefficient is
\(d^{-1}(\det g)C(g^{-\mathsf T})\), and the square test is the
positive-phase transform for \(a\). The factors come from the inducing
list \(e_i d\), and the epsilon factor uses parameter \(a\).

The proof twists the standard vector by \(d\circ\det\) and gives the
compact weight the inverse twist. These twists cancel on the compact
integration variable. Inverse transpose inverts the determinant,
which identifies the reflected coefficient. Applying the Library's
square coefficient functional equation at \(-a\) supplies absolute
integrability in a common right half-plane and entire normalized
continuations with the stated reflection.

This is the determinant twist in the square integrals in Section 8.3
of Hervé Jacquet, *Archimedean Rankin–Selberg Integrals*, 2009, DOI
`10.1090/conm/489/09547`, using the square equation of Proposition 4.4.

`complexAdjacentTwistedZetaGrowth` retains exponential strip growth of the two normalized functions. The determinant twist changes the input vector and the compact weight. The proof uses the square coefficient theorem with strip growth for this vector and transports the same functions along the kernel identities.
