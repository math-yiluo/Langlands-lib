# Cartan coverings for any generic diagonal cocharacter of the general linear group

The theorem `generalLinearGenericCartanCovering` proves
`GeneralLinearGenericCartanCoveringStatement`. Fix a nonarchimedean
local field \(F\), a size \(N\), the diagonal torus
\(i : T \to \mathrm{GL}_N\), the standard integral subgroup \(K\) and a
generic cocharacter \(\nu\). Both coverings use the singleton
consisting of the identity for the finite set of centralizer factors.

**Chamber membership.** The private lemma
`uniformizerSection_mem_CAplus` shows that the uniformizer power
\(\varpi^c\), the value of `uniformizerSection` at \(c\), lies in the
simple-root chamber `CocharacterUniformizer.CAplus F T J` when
\(\langle \alpha, c\rangle \ge 0\) for every \(\alpha \in J\). By
`uniformizerSection_eq_latticeSection` and
`CocharacterUniformizer.characterNorm_latticeSection`, the
residue-normalized norm of \(\alpha\) at \(\varpi^c\) is
\(q^{-\langle\alpha,c\rangle}\). This is at most \(1\) because the residue
cardinality satisfies \(q > 1\).

**Ambient covering.** Let \(g \in \mathrm{GL}_N(F)\). Surjectivity in
`generalLinearIntegralCartan` gives a point \(x\) of `C0Plus` for the
positive roots of \(\nu\) with \(KgK = KxK\), so \(g = k_1 x k_2\) with
\(k_1, k_2 \in K\). By `mem_C0Plus`, \(x = i(\varpi^c)\) for a
cocharacter \(c\) whose pairings with all positive roots are
nonnegative. The simple roots are positive
(`simpleRelativeRoots_subset_positive`), so \(\varpi^c\) lies in the
simple-root chamber. Then \(g = k_1 \cdot 1 \cdot i(\varpi^c) \cdot k_2\).

**Levi covering.** Let \(J\) be a set of simple roots and \(m\) a
point of the standard Levi \(M_J(F)\). Write
\(j\) = `Standard.leviHom i ν J` for the Levi inclusion and
\(K_J = j^{-1}(K)\). The inclusion represents the standard Levi
(`Standard.isRepresentedBy_leviHom`), so \(m = j(m')\) for a rational
point \(m'\) of the Levi scheme. Surjectivity in
`generalLinearIntegralLeviCartan` gives \(m' = k_1 x k_2\) with
\(k_1, k_2 \in K_J\). Here \(x\) is a point of `C0Plus` for the Levi
torus map `Standard.leviTorusHom i ν J` and its positive roots. By
`mem_C0Plus`, \(x\) is the image of \(\varpi^c\) for a cocharacter
\(c\) with nonnegative pairings against these roots. Every root of
\(J\) is among them
(`Aubert.General.mem_positiveRelativeRoots_leviTorusHom`), so
\(\varpi^c\) lies in the chamber of \(J\). The images \(j(k_1)\) and
\(j(k_2)\) lie in \(K\) by the definition of \(K_J\). They lie in
\(M_J(F)\) because they are in the range of \(j\). The Levi torus map
factors \(i\) through \(j\) (`Standard.leviTorusHom_comp`), so
\(j(x) = i(\varpi^c)\). Applying \(j\) to \(m' = k_1 x k_2\) gives
\(m = j(k_1) \cdot 1 \cdot i(\varpi^c) \cdot j(k_2)\).

The statement comes from Renard's Cartan decomposition V.5.1(4), its
inheritance by standard Levis in V.5.1(5) and the uniformizer section of
V.3.23. See David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, printed pp. 117 and 122
(PDF pp. 123 and 128).
