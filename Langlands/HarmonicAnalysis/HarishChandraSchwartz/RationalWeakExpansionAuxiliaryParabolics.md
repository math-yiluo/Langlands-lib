# Auxiliary parabolics for the weak-expansion c-family

This derived geometry unit constructs the actual ambient parabolics used by
Waldspurger's c-family. Its analytic operators and identities remain separate.
The field has arbitrary characteristic; there is no representation parameter.

Waldspurger, *La formule de Plancherel pour les groupes p-adiques d'après
Harish-Chandra* (2003), V.1, printed pp.288–289, defines

\[
P_s=(M'\cap sP)U',\qquad \widetilde P_s=(M'\cap sP)\overline U'.
\]

These are parabolics of the original group, with Levi \(sM\), even though the
lower coefficient and packet space lives on \(M'\). The two standard integrals
in the definition of \(c_{P'|P}(s,\omega)\) have these ambient targets. The
construction here makes those groups accessible to the published
`DynamicCommonLeviComposition.pairFamily` and nested induction APIs.

`auxiliaryMultiplicity i α β` chooses a natural number from the published
`Dynamic.exists_dominant_inclusions`. `auxiliaryCocharacter i α β` is
\(N\alpha+\beta=\beta+N\alpha\). The finite-type construction guarantees the all-test
inclusions \(P(\beta+N\alpha)\subseteq P(\alpha)\),
\(U(\alpha)\subseteq U(\beta+N\alpha)\), and
\(Z(\beta+N\alpha)\subseteq Z(\alpha)\).
`auxiliaryCocharacter_spec` also proves
\(Z(\beta+N\alpha)=Z(\alpha)\cap Z(\beta)\).
For that last equality, cocharacters centralizing a point form the published
integer submodule `Dynamic.centralizingCocharacters`; subtracting \(N\alpha\)
from \(\beta+N\alpha\) recovers \(\beta\).

Take \(\beta=s\zeta\), where \(\zeta\) defines the original standard parabolic.
`cParabolicCocharacter i ζ' ζ n` uses \(\alpha=\zeta'\);
`cOppositeParabolicCocharacter` uses \(\alpha=-\zeta'\).
Here \(\zeta'\) is standard for \(I'\), so both outer centralizers are the
actual standard Levi \(M'\). If the chosen Weyl representative satisfies
\(sM\subseteq M'\), the centralizer intersection above is exactly \(sM\).

`auxiliaryParabolic_geometry` is stated for any outer cocharacter whose
centralizer is \(M'\), covering both signs. It proves the common-centralizer
identity, `Dynamic.IsCompatibleNestedPair`, the all-test pullback
\(P(\beta+N\alpha)\cap M'=M'\cap sP\), and the exact parabolic and radical
extensions by \(U(\alpha)\). The product is the existing
`Dynamic.extendFromCentralizer`, whose membership formula is literally
\(j'(l)u\). Thus the ambient parabolics are the source's displayed products,
without transporting the lower parabolic to standard data.

`cParabolicCocharacter_spec` and `cOppositeParabolicCocharacter_spec`
specialize the centralizer, nested-pair and pullback conclusions to a supplied
standard outer cocharacter and its negative. They also assume the outer root
index is a subset of the simple relative roots, as needed by the published
standard-cocharacter agreement. The negative specialization uses
`Dynamic.centralizer_groupHom_neg`; its full product formula follows from
`auxiliaryParabolic_geometry` with the same centralizer agreement.

The orbit argument uses the published
`Dynamic.orbit_add_zsmul_of_mem_centralizer`: on \(Z(\alpha)\), adding
\(N\alpha\) leaves the conjugation orbit unchanged. The published
`Dynamic.realization_of_inclusions` then supplies the exact extension
formulas. The earlier `lowerCocharacter_dynamic` identifies the lower
parabolic and radical with their actual intersection functors.

These are imported constructions and new derived adapters, with their
agreement lemmas proved here. No c-family regularity, expansion, finite
decomposition, packet identity, representation bound, or measure compatibility
is assumed or asserted.
