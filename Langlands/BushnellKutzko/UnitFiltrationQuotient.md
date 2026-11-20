# From filtered units to an additive quotient

This supporting construction is derived from the positive-depth unit groups in
Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), §1.1, printed pp. 21–22 (registered as
`bushnell-kutzko-1993-admissible-dual-gln`). It supplies the group map used to
prove (1.1.5)–(1.1.6).

Write \(P^i\) for `𝓛.endFiltration i` and \(U^i\) for `𝓛.unitFiltration i`.
For natural indices \(i,j\) with \(j\le 2i\),
`LatticeChain.unitFiltrationToQuotient` sends \(g\in U^i\) to the class of
\(g-1\) in \(P^i/(P^i\cap P^j)\). The quotient uses the comap of \(P^j\)
along the inclusion of \(P^i\), and `Multiplicative` makes its additive
operation available as the target operation of a monoid homomorphism. The
difference between \(gh-1\) and \((g-1)+(h-1)\) is \((g-1)(h-1)\).
`mul_mem_endFiltration` places this product in \(P^{2i}\), which lies in
\(P^j\) by antitonicity, so the two representatives give the same class.

For \(i\ge 1\), `unitFiltrationToQuotient_surjective` takes a representative
\(x\in P^i\) of an arbitrary class and uses `exists_mem_unitFiltration` to
obtain the unit \(1+x\) in \(U^i\). `mem_ker_unitFiltrationToQuotient` uses
`Submodule.Quotient.mk_eq_zero` to identify the kernel with the units in
\(U^i\) that also lie in \(U^j\). Their membership in the order, and that of
their inverses, already follows from membership in \(U^i\), so the only
additional condition is \(g-1\in P^j\). When \(i\le j\), this kernel is
\(U^j\) viewed as a subgroup of \(U^i\).
