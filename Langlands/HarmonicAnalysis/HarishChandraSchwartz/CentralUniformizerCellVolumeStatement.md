# Double-coset volume on the central uniformizer quotient

Let \(G\) be a connected reductive group over a nonarchimedean local field
and \(A_G\) its split component. Use the canonical topology on \(G(F)\).
Let \(C=C_{A_G}\) be the ambient image of the cocharacters of \(A_G\)
evaluated at the chosen uniformizer, implemented by `RenardCartan.C0`.
Write \(q:G(F)\to C\backslash G(F)\) for the quotient map. The centrality
of \(C\) identifies this left quotient with the book's central quotient.

For each compact open subgroup \(K\) and each \(g\in G(F)\), the
proposition asserts that \(q\) is injective on \(D=KgK\).
If left Haar measure \(\mu_G\) and the quotient measure \(\mu_Q\) are
compatible with counting measure on \(C\) in the sense of the Weil
formula, then
\[
  \mu_Q(q(D))=\mu_G(D).
\]
All three measures use the indicated Borel spaces. The proposition
applies to the individual Cartan cells in the sum in VII.1.2.

This measure comparison uses the part of the book's calculation that
assigns the ambient double-coset mass to each quotient cell. The norm
kernel contains \(K\), so the rational-character valuation is constant
on \(D\). Its restriction to \(C\) is injective, which gives the stated
injectivity on each cell. Counting measure and the Weil formula give the
normalization of the two masses. Distinct labels in the Cartan cover
may still describe the same cell. [Cartan cover correction](../../../notes/errata/renard-vii12-cartan-cover.md)

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026. VII.1.2, the weights in the expansion preceding
(VII.1.2.2), printed pp. 221–222 (PDF pp. 227–228). The compatibility
formula is in II.3.9, printed pp. 48–50 (PDF pp. 54–56).
The norm kernel and uniformizer lattice are in V.2.3 and V.2.5–6,
printed pp. 105–108 (PDF pp. 111–114). Registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
