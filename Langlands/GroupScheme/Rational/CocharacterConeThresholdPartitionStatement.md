# The threshold partition of the integral cocharacter cone

Fix a commutative group scheme \(T\) over a field and a finite set \(R\) of
its actual characters. For each \(\alpha\in R\), choose a cocharacter
\(t_\alpha\) with \(d_\alpha=\langle\alpha,t_\alpha\rangle>0\) and
\(\langle\beta,t_\alpha\rangle=0\) for every other \(\beta\in R\). Let
\(A\) be the common integral annihilator of \(R\). The target cone is
`CocharacterCone.quotient T R`, the nonnegative cocharacter cone modulo
\(A\). The residue set consists of those classes \(r\) having pairings
\(0\le\langle\alpha,r\rangle<d_\alpha\) for all \(\alpha\in R\).
The pairings are independent of the representative of \(r\).

The proposition states that the residue set is finite and that for each
cutoff \(n\ge0\), the target cone is in bijection with tuples
\((J,r,b,\ell)\). Here \(J\subseteq R\), \(r\) is a residue,
\(b:J\to\{0,\ldots,n\}\), and \(\ell:R\setminus J\to\mathbb N\).
The required bijection sends a tuple to
\[
  r+\sum_{\alpha\in J}b(\alpha)[t_\alpha]
    +\sum_{\alpha\notin J}(n+1+\ell(\alpha))[t_\alpha].
\]
Consequently the pieces indexed by \(J\) are disjoint and each has a finite
set of bounded parts, given by \(r\) and \(b\). The complementary ray
exponents are strictly bigger than \(n\). For empty \(R\) the annihilator
is the whole cocharacter lattice and there is one tuple and one cone class.

This is the threshold splitting into \(S_M(n)_1 S'_M(n)\) after
(VII.1.2.2), corrected to account for the finite residue set. The printed
identification of the whole monoid with \(\mathbb N^{|R|}\) can fail.
For the diagonal torus of \(\mathrm{SL}_3\) the simple-root coordinate image
consists of \((p,q)\) with \(p\equiv q\pmod 3\). The rays with coordinates
\((3,0)\) and \((0,3)\) leave three residues in their fundamental box.

For the source application take \(R\) to be the set of simple relative
roots of a maximal split torus. `standardCocharacter` for the complement
of each single root supplies the chosen rays. Each \(J\) then specifies
the Levi of a standard parabolic. `coneQuotientComparison` transports the
cocharacter classes to the actual common-uniformizer quotient modulo the
split component of the ambient group. The complementary ray sums pair
to zero on the simple roots of \(J\), as required for the Levi split
component. [Cocharacter cone](CocharacterCone.md) ·
[Uniformizer quotient comparison](../../Geometry/Building/CocharacterUniformizerConeQuotientProof.md)

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026. VII.1.2, the threshold partition after
(VII.1.2.2), printed pp. 222–223 (PDF pp. 228–229), using the chamber
quotient in V.3.24, printed p. 117 (PDF p. 123). Registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
