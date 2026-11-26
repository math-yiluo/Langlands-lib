# The central simple algebra of a signed split-place profile

`Langlands.Shimura.FiniteUnitary.signedSplitBrauerProfile` extends prescribed
signed \(n\)-torsion values at the two places above each selected split
place to the finite places of the supplied CM field \(K\).
`exists_csa_for_splitProfile` realizes these values by a single degree-\(n\)
central simple algebra over \(K\). The invariant is zero above each finite
place outside the support. Each value is exhibited on the actual completed
algebra over the corresponding completion of \(K\).

The orientation identifies the two places above a selected place with
`Fin 2`. The map from the product of the selected places and `Fin 2` to
the finite places of \(K\) is injective because an upper place determines
its lower place and its orientation index. Extend the signed values by
zero. They are all killed by \(n\), and their sum vanishes because the
two values above each selected place are additive inverses. The
prescribed-degree Brauer realization theorem
`Langlands.Brauer.numberFieldBrauerProfileRealization` therefore supplies
the algebra. Its scalar extensions are the representatives used in the
completion predicates.

This is the Brauer algebra construction for the split-place data in
Clozel's unitary profile criterion, §2.1, printed pp. 102–105. It uses
the actual signed values of `UnitaryLocalProfileRealizationStatement`
and the Library's totally complex Brauer profile theorem. The registered
source `clozel-1991-selfdual-galois` has SHA-256
`9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac`.
