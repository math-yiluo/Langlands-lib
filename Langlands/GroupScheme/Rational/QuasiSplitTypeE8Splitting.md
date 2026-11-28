# Splitting of quasi-split simply connected groups of type \(E_8\)

`QuasiSplitTypeE8SplittingStatement` says that an affine, locally finite-type,
simply connected quasi-split group scheme over a field \(K\) has a split maximal
\(K\)-torus if its actual Tits index has simple vertices numbered by `Fin 8`
with Cartan matrix `CartanMatrix.E 8`. The field ranges over an arbitrary universe.

First, `TitsIndexData.starAction_eq_one_of_typeE8` uses
`CartanENumbering.rigid_eight` to show that the absolute star action fixes each
simple vertex. This step applies to all simply connected groups with the given
Cartan matrix. Simple connectedness ascends to the separable closure, so
`splitSimplyConnectedCorootSpanIndependent` supplies integral spanning by the
coroots of the split pinning. The simple coroots span the same lattice, and
`InnerTypeANormOneReduction.aut_eq_one_of_simple` upgrades pointwise fixedness
of the simple vertices to triviality on the full based root datum.

`quasiSplitTypeE8Splitting` applies the absolute criterion
`quasiSplitStarCriterion` to this trivial action, giving the claimed split
maximal torus under the quasi-split hypothesis.
