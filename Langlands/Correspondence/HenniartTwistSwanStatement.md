# Swan exponents of character twists of supercuspidal classes

Write \(n=k+1\) for the positive rank, represented by `k.succPNat` in Lean.
The field \(K\) is a `PadicField.{uK} p` for a prime \(p\). The field universe
`uK` and the representation universe `uV` are independent.

## Definitions in `Langlands.Henniart.Numerical`

A character \(\chi\) of \(K^\times\) is a `Correspondence.QuasiCharacter K`,
the Library's type of continuous homomorphisms \(K^\times\to\mathbb C^\times\)
for the canonical topology of \(K\).

`characterSwanExponent K χ` is the Library's canonical
`multiplicativeConductor` \(a(\chi)\) minus one, with truncated subtraction in
`ℕ`. The conductor is the least index at which \(\chi\) is trivial on the
unit filtration, whose level zero is \(\mathcal O_K^\times\) and whose level
\(i\ge1\) is \(U_K^i=1+\mathfrak p_K^i\). The Swan exponent is zero when
\(\chi\) is trivial on \(U_K^1\), including the unramified and tamely ramified
cases. Otherwise it is the least \(t\ge1\) with \(\chi\) trivial on
\(U_K^{t+1}\). In particular \(a(\chi)=\operatorname{sw}(\chi)+1\) for ramified
characters, as in §2.2 of the route note.

`supercuspidalCharacterTwist K k χ` is the equivalence of rank-\(n\)
supercuspidal classes sending \(\pi\) to \((\chi\circ\det)\otimes\pi\).
It uses the published `Correspondence.supercuspidalTwistEquiv` and realizes
the determinant twist in §4.4 of the route note. The inverse twists by
\(\chi^{-1}\). The underlying homomorphism of
`K.canonicalTopologicalData.unramifiedCharacterContinuous z` sends \(x\) to
\(z^{\operatorname{ord}_K(x)}\). Its determinant pullback is the one used
by `supercuspidalUnramifiedTwist K k z`. Applying either equivalence to a
class gives definitionally equal results.

## Statement in `Langlands.Henniart`

`SupercuspidalTwistSwanBoundStatement.{uK, uV}` says that for every prime
\(p\), field \(K\) as above, rank \(n=k+1\), character \(\chi\), and
supercuspidal class \(\pi\) with `HasSupercuspidalSwan K π s`, the twist
has a Swan exponent \(s'\) satisfying
\[
s'\le \max(s,n\operatorname{sw}(\chi)).
\]
Equality holds whenever \(s\) and \(n\operatorname{sw}(\chi)\) differ.
The class exponents \(s\) and \(s'\) use `Numerical.HasSupercuspidalSwan` from
`Langlands.Correspondence.HenniartRefinedStrata`. This predicate requires
a finite first fixed-vector level \(a\) and takes the truncated difference
\(a-n\). The conclusion thus includes finiteness of the twist's conductor.

## Provenance

This proposition formalizes the supercuspidal conclusion of Lemma
`lem:level`(ii), an internal result in the operator's *The numerical local
Langlands correspondence for GL_n: counts on the two sides and the
recommended route of proof* (`operator-numerical-llc-route-2026-11-16`,
`numerical-LLC-route.tex`, §4.4, lines 615–643). The note proves the result
by controlling normalized levels under determinant twists and uses part
(i) to pass from levels to Swan exponents. Its §§2.1 and 4.4 explain the
comparison between the first fixed-vector level and the epsilon-factor
conductor used in the paper argument.

The inputs to part (i) include Bushnell, *Hereditary orders, Gauss sums and
supercuspidal representations of GL_N* (1987,
`bushnell-1987-hereditary-orders-gauss-sums`), Theorems 1 and 2′, printed
pp. 192 and 196–197, and Bushnell–Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993, `bushnell-kutzko-1993-admissible-dual-gln`),
§2.3, especially (2.3.1) and (2.3.2) on printed p. 57.

Henniart, *La conjecture de Langlands locale numérique pour GL(n)* (1988,
`henniart-1988-numerical`), §6.7, printed p. 520, uses the Jacquet–Langlands
correspondence with representations of division algebras to obtain the
inequality and its equality clause.
