# Formal intertwining and conjugacy of simple strata

`Langlands.BushnellKutzko.SimpleStratumConjugacyStatement` states two
results over every nonarchimedean local field \(F\) and finite-dimensional
\(F\)-space \(V\).

1. Let \(S=[\mathfrak A,n,r,\beta_1]\) and \(T=[\mathfrak A,n,r,\beta_2]\)
   be simple. Nonemptiness of `T.formalIntertwining S` means that a unit
   of \(\operatorname{End}_F(V)\) conjugates some element of \(T\)'s
   coset into \(S\)'s coset. The conclusion gives \(u\in U(\mathfrak A)\)
   with \(u\beta_2u^{-1}\in S.\mathrm{coset}\). At the fixed order and
   depth, membership means that the coset of \(u\beta_2u^{-1}\) equals
   the coset of \(\beta_1\), which is stratum equivalence.
2. For \(n\geq 1\), let \(S=[\mathfrak A,n,n-1,b]\) be equivalent
   to a simple stratum \(T\), and let \(Z=[\mathfrak A,n,n-1,0]\).
   Then `S.formalIntertwining Z` is empty. By BK93 (2.3.2) the
   simple stratum at this depth is fundamental, and fundamentality
   is invariant under equivalence. For the same order and levels the
   inequality of (2.6.2) is \((n-1)/e(\mathfrak A)<n/e(\mathfrak A)\).
   Intertwining with \(Z\) would therefore contradict fundamentality.

Equality of `chain.order` expresses the common hereditary order.
`chain.unitFiltration 0` is its unit group. The results also apply
over \(E=F[\gamma]\) in \(\operatorname{End}_E(V)\) by specializing the
base field to \(E\). The spectral structures of
`Langlands.LocalField.FiniteExtension` make the finite extension a
nonarchimedean local field. `isIntegral_iff_mem_spectralInteger`
identifies the valuation-ring elements with the integral closure, and
`LatticeChain.relativeLatticeChain` gives the chain for the relative
order with the same lattices and restricted endomorphism filtration.

Source. C. J. Bushnell and P. C. Kutzko, *The admissible dual of
GL(N) via compact open subgroups*, Annals of Mathematics Studies 129
(1993), (2.6.1), printed p. 83, and (2.3.2), (2.6.2), printed
pp. 57 and 86 (PDF pp. 95, 69 and 98). The registered source is
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
